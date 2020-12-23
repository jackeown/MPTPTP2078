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
% DateTime   : Thu Dec  3 11:58:59 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  110 (8284 expanded)
%              Number of clauses        :   65 (2841 expanded)
%              Number of leaves         :   12 (2246 expanded)
%              Depth                    :   36
%              Number of atoms          :  517 (53924 expanded)
%              Number of equality atoms :  412 (35675 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f17,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( X3 != X5
          & k3_mcart_1(X5,X6,X7) = X4
          & m1_subset_1(X7,X2) )
     => ( X3 != X5
        & k3_mcart_1(X5,X6,sK2(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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

fof(f15,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f17,f16,f15])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f29,f22])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f30,f22])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f31,f22])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k6_mcart_1(sK3,sK4,sK5,sK7) != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK6 = X6
                  | k3_mcart_1(X5,X6,X7) != sK7
                  | ~ m1_subset_1(X7,sK5) )
              | ~ m1_subset_1(X6,sK4) )
          | ~ m1_subset_1(X5,sK3) )
      & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK6 = X6
                | k3_mcart_1(X5,X6,X7) != sK7
                | ~ m1_subset_1(X7,sK5) )
            | ~ m1_subset_1(X6,sK4) )
        | ~ m1_subset_1(X5,sK3) )
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f14,f19])).

fof(f34,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f34,f22])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f32,f21,f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f36,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X6
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X6
      | k4_tarski(k4_tarski(X5,X6),X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f35,f21])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f39,plain,(
    k6_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k3_mcart_1(X4,X5,X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f27,f21,f22])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(equality_resolution,[],[f44])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(sK0(X1,X2,X3,X4,X0),X1)
    | k5_mcart_1(X1,X2,X3,X0) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_374,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2,X4,X3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(sK1(X1,X2,X3,X4,X0),X2)
    | k5_mcart_1(X1,X2,X3,X0) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_375,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2,X4,X3),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(sK2(X1,X2,X3,X4,X0),X3)
    | k5_mcart_1(X1,X2,X3,X0) = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_376,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
    | m1_subset_1(sK2(X0,X1,X2,X4,X3),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_372,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = X4
    | k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X0),sK1(X1,X2,X3,X4,X0)),sK2(X1,X2,X3,X4,X0)) = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_377,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = X4
    | k4_tarski(k4_tarski(sK0(X0,X1,X2,X4,X3),sK1(X0,X1,X2,X4,X3)),sK2(X0,X1,X2,X4,X3)) = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1994,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) = X0
    | k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_372,c_377])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_382,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1057,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_372,c_382])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_157,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_176,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_158,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_554,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_555,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_556,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_557,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_558,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_559,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_1461,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1057,c_14,c_13,c_12,c_176,c_555,c_557,c_559])).

cnf(c_2063,plain,
    ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1994,c_1461])).

cnf(c_2568,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = X0
    | k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_14,c_13,c_12,c_176,c_555,c_557,c_559])).

cnf(c_2569,plain,
    ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(renaming,[status(thm)],[c_2568])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ m1_subset_1(X1,sK4)
    | ~ m1_subset_1(X2,sK3)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK7
    | sK6 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_373,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
    | sK6 = X1
    | m1_subset_1(X2,sK5) != iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2574,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | m1_subset_1(sK2(sK3,sK4,sK5,X0,sK7),sK5) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2569,c_373])).

cnf(c_2693,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_376,c_2574])).

cnf(c_2694,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2693,c_1461])).

cnf(c_17,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2709,plain,
    ( m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
    | sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2694,c_17,c_14,c_13,c_12,c_176,c_555,c_557,c_559])).

cnf(c_2710,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2709])).

cnf(c_2719,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_375,c_2710])).

cnf(c_2720,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2719,c_1461])).

cnf(c_2725,plain,
    ( m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
    | sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2720,c_17,c_14,c_13,c_12,c_176,c_555,c_557,c_559])).

cnf(c_2726,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2725])).

cnf(c_2734,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_374,c_2726])).

cnf(c_2735,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2734,c_1461])).

cnf(c_2740,plain,
    ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2735,c_17,c_14,c_13,c_12,c_176,c_555,c_557,c_559])).

cnf(c_2746,plain,
    ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK6),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(superposition,[status(thm)],[c_2740,c_2569])).

cnf(c_2802,plain,
    ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
    | k4_tarski(sK7,X1) != sK7
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | m1_subset_1(X1,sK5) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
    | m1_subset_1(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK6),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2746,c_373])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_383,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1250,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_372,c_383])).

cnf(c_1628,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1250,c_14,c_13,c_12,c_176,c_555,c_557,c_559])).

cnf(c_11,negated_conjecture,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1631,plain,
    ( k2_mcart_1(k1_mcart_1(sK7)) != sK6 ),
    inference(demodulation,[status(thm)],[c_1628,c_11])).

cnf(c_4,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
    | k6_mcart_1(X3,X4,X5,k4_tarski(k4_tarski(X0,X1),X2)) = X1
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_380,plain,
    ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X4
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2808,plain,
    ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X3,sK7),sK6),sK2(sK3,sK4,sK5,X3,sK7))) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2746,c_380])).

cnf(c_3004,plain,
    ( k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK6),sK2(sK3,sK4,sK5,X0,sK7))) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_372,c_2808])).

cnf(c_3028,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = X0
    | k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK6),sK2(sK3,sK4,sK5,X0,sK7))) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3004,c_14,c_13,c_12,c_176,c_555,c_557,c_559])).

cnf(c_3029,plain,
    ( k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK6),sK2(sK3,sK4,sK5,X0,sK7))) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(renaming,[status(thm)],[c_3028])).

cnf(c_3033,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) = sK6
    | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(superposition,[status(thm)],[c_2746,c_3029])).

cnf(c_3034,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = X0
    | k2_mcart_1(k1_mcart_1(sK7)) = sK6 ),
    inference(demodulation,[status(thm)],[c_3033,c_1628])).

cnf(c_3037,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2802,c_1631,c_3034])).

cnf(c_3286,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_3037,c_3037])).

cnf(c_3551,plain,
    ( k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_3286,c_14])).

cnf(c_3553,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3551,c_3286])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.69/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/1.00  
% 2.69/1.00  ------  iProver source info
% 2.69/1.00  
% 2.69/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.69/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/1.00  git: non_committed_changes: false
% 2.69/1.00  git: last_make_outside_of_git: false
% 2.69/1.00  
% 2.69/1.00  ------ 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options
% 2.69/1.00  
% 2.69/1.00  --out_options                           all
% 2.69/1.00  --tptp_safe_out                         true
% 2.69/1.00  --problem_path                          ""
% 2.69/1.00  --include_path                          ""
% 2.69/1.00  --clausifier                            res/vclausify_rel
% 2.69/1.00  --clausifier_options                    --mode clausify
% 2.69/1.00  --stdin                                 false
% 2.69/1.00  --stats_out                             all
% 2.69/1.00  
% 2.69/1.00  ------ General Options
% 2.69/1.00  
% 2.69/1.00  --fof                                   false
% 2.69/1.00  --time_out_real                         305.
% 2.69/1.00  --time_out_virtual                      -1.
% 2.69/1.00  --symbol_type_check                     false
% 2.69/1.00  --clausify_out                          false
% 2.69/1.00  --sig_cnt_out                           false
% 2.69/1.00  --trig_cnt_out                          false
% 2.69/1.00  --trig_cnt_out_tolerance                1.
% 2.69/1.00  --trig_cnt_out_sk_spl                   false
% 2.69/1.00  --abstr_cl_out                          false
% 2.69/1.00  
% 2.69/1.00  ------ Global Options
% 2.69/1.00  
% 2.69/1.00  --schedule                              default
% 2.69/1.00  --add_important_lit                     false
% 2.69/1.00  --prop_solver_per_cl                    1000
% 2.69/1.00  --min_unsat_core                        false
% 2.69/1.00  --soft_assumptions                      false
% 2.69/1.00  --soft_lemma_size                       3
% 2.69/1.00  --prop_impl_unit_size                   0
% 2.69/1.00  --prop_impl_unit                        []
% 2.69/1.00  --share_sel_clauses                     true
% 2.69/1.00  --reset_solvers                         false
% 2.69/1.00  --bc_imp_inh                            [conj_cone]
% 2.69/1.00  --conj_cone_tolerance                   3.
% 2.69/1.00  --extra_neg_conj                        none
% 2.69/1.00  --large_theory_mode                     true
% 2.69/1.00  --prolific_symb_bound                   200
% 2.69/1.00  --lt_threshold                          2000
% 2.69/1.00  --clause_weak_htbl                      true
% 2.69/1.00  --gc_record_bc_elim                     false
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing Options
% 2.69/1.00  
% 2.69/1.00  --preprocessing_flag                    true
% 2.69/1.00  --time_out_prep_mult                    0.1
% 2.69/1.00  --splitting_mode                        input
% 2.69/1.00  --splitting_grd                         true
% 2.69/1.00  --splitting_cvd                         false
% 2.69/1.00  --splitting_cvd_svl                     false
% 2.69/1.00  --splitting_nvd                         32
% 2.69/1.00  --sub_typing                            true
% 2.69/1.00  --prep_gs_sim                           true
% 2.69/1.00  --prep_unflatten                        true
% 2.69/1.00  --prep_res_sim                          true
% 2.69/1.00  --prep_upred                            true
% 2.69/1.00  --prep_sem_filter                       exhaustive
% 2.69/1.00  --prep_sem_filter_out                   false
% 2.69/1.00  --pred_elim                             true
% 2.69/1.00  --res_sim_input                         true
% 2.69/1.00  --eq_ax_congr_red                       true
% 2.69/1.00  --pure_diseq_elim                       true
% 2.69/1.00  --brand_transform                       false
% 2.69/1.00  --non_eq_to_eq                          false
% 2.69/1.00  --prep_def_merge                        true
% 2.69/1.00  --prep_def_merge_prop_impl              false
% 2.69/1.00  --prep_def_merge_mbd                    true
% 2.69/1.00  --prep_def_merge_tr_red                 false
% 2.69/1.00  --prep_def_merge_tr_cl                  false
% 2.69/1.00  --smt_preprocessing                     true
% 2.69/1.00  --smt_ac_axioms                         fast
% 2.69/1.00  --preprocessed_out                      false
% 2.69/1.00  --preprocessed_stats                    false
% 2.69/1.00  
% 2.69/1.00  ------ Abstraction refinement Options
% 2.69/1.00  
% 2.69/1.00  --abstr_ref                             []
% 2.69/1.00  --abstr_ref_prep                        false
% 2.69/1.00  --abstr_ref_until_sat                   false
% 2.69/1.00  --abstr_ref_sig_restrict                funpre
% 2.69/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.00  --abstr_ref_under                       []
% 2.69/1.00  
% 2.69/1.00  ------ SAT Options
% 2.69/1.00  
% 2.69/1.00  --sat_mode                              false
% 2.69/1.00  --sat_fm_restart_options                ""
% 2.69/1.00  --sat_gr_def                            false
% 2.69/1.00  --sat_epr_types                         true
% 2.69/1.00  --sat_non_cyclic_types                  false
% 2.69/1.00  --sat_finite_models                     false
% 2.69/1.00  --sat_fm_lemmas                         false
% 2.69/1.00  --sat_fm_prep                           false
% 2.69/1.00  --sat_fm_uc_incr                        true
% 2.69/1.00  --sat_out_model                         small
% 2.69/1.00  --sat_out_clauses                       false
% 2.69/1.00  
% 2.69/1.00  ------ QBF Options
% 2.69/1.00  
% 2.69/1.00  --qbf_mode                              false
% 2.69/1.00  --qbf_elim_univ                         false
% 2.69/1.00  --qbf_dom_inst                          none
% 2.69/1.00  --qbf_dom_pre_inst                      false
% 2.69/1.00  --qbf_sk_in                             false
% 2.69/1.00  --qbf_pred_elim                         true
% 2.69/1.00  --qbf_split                             512
% 2.69/1.00  
% 2.69/1.00  ------ BMC1 Options
% 2.69/1.00  
% 2.69/1.00  --bmc1_incremental                      false
% 2.69/1.00  --bmc1_axioms                           reachable_all
% 2.69/1.00  --bmc1_min_bound                        0
% 2.69/1.00  --bmc1_max_bound                        -1
% 2.69/1.00  --bmc1_max_bound_default                -1
% 2.69/1.00  --bmc1_symbol_reachability              true
% 2.69/1.00  --bmc1_property_lemmas                  false
% 2.69/1.00  --bmc1_k_induction                      false
% 2.69/1.00  --bmc1_non_equiv_states                 false
% 2.69/1.00  --bmc1_deadlock                         false
% 2.69/1.00  --bmc1_ucm                              false
% 2.69/1.00  --bmc1_add_unsat_core                   none
% 2.69/1.00  --bmc1_unsat_core_children              false
% 2.69/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.00  --bmc1_out_stat                         full
% 2.69/1.00  --bmc1_ground_init                      false
% 2.69/1.00  --bmc1_pre_inst_next_state              false
% 2.69/1.00  --bmc1_pre_inst_state                   false
% 2.69/1.00  --bmc1_pre_inst_reach_state             false
% 2.69/1.00  --bmc1_out_unsat_core                   false
% 2.69/1.00  --bmc1_aig_witness_out                  false
% 2.69/1.00  --bmc1_verbose                          false
% 2.69/1.00  --bmc1_dump_clauses_tptp                false
% 2.69/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.00  --bmc1_dump_file                        -
% 2.69/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.00  --bmc1_ucm_extend_mode                  1
% 2.69/1.00  --bmc1_ucm_init_mode                    2
% 2.69/1.00  --bmc1_ucm_cone_mode                    none
% 2.69/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.00  --bmc1_ucm_relax_model                  4
% 2.69/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.00  --bmc1_ucm_layered_model                none
% 2.69/1.00  --bmc1_ucm_max_lemma_size               10
% 2.69/1.00  
% 2.69/1.00  ------ AIG Options
% 2.69/1.00  
% 2.69/1.00  --aig_mode                              false
% 2.69/1.00  
% 2.69/1.00  ------ Instantiation Options
% 2.69/1.00  
% 2.69/1.00  --instantiation_flag                    true
% 2.69/1.00  --inst_sos_flag                         false
% 2.69/1.00  --inst_sos_phase                        true
% 2.69/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel_side                     num_symb
% 2.69/1.00  --inst_solver_per_active                1400
% 2.69/1.00  --inst_solver_calls_frac                1.
% 2.69/1.00  --inst_passive_queue_type               priority_queues
% 2.69/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.00  --inst_passive_queues_freq              [25;2]
% 2.69/1.00  --inst_dismatching                      true
% 2.69/1.00  --inst_eager_unprocessed_to_passive     true
% 2.69/1.00  --inst_prop_sim_given                   true
% 2.69/1.00  --inst_prop_sim_new                     false
% 2.69/1.00  --inst_subs_new                         false
% 2.69/1.00  --inst_eq_res_simp                      false
% 2.69/1.00  --inst_subs_given                       false
% 2.69/1.00  --inst_orphan_elimination               true
% 2.69/1.00  --inst_learning_loop_flag               true
% 2.69/1.00  --inst_learning_start                   3000
% 2.69/1.00  --inst_learning_factor                  2
% 2.69/1.00  --inst_start_prop_sim_after_learn       3
% 2.69/1.00  --inst_sel_renew                        solver
% 2.69/1.00  --inst_lit_activity_flag                true
% 2.69/1.00  --inst_restr_to_given                   false
% 2.69/1.00  --inst_activity_threshold               500
% 2.69/1.00  --inst_out_proof                        true
% 2.69/1.00  
% 2.69/1.00  ------ Resolution Options
% 2.69/1.00  
% 2.69/1.00  --resolution_flag                       true
% 2.69/1.00  --res_lit_sel                           adaptive
% 2.69/1.00  --res_lit_sel_side                      none
% 2.69/1.00  --res_ordering                          kbo
% 2.69/1.00  --res_to_prop_solver                    active
% 2.69/1.00  --res_prop_simpl_new                    false
% 2.69/1.00  --res_prop_simpl_given                  true
% 2.69/1.00  --res_passive_queue_type                priority_queues
% 2.69/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.00  --res_passive_queues_freq               [15;5]
% 2.69/1.00  --res_forward_subs                      full
% 2.69/1.00  --res_backward_subs                     full
% 2.69/1.00  --res_forward_subs_resolution           true
% 2.69/1.00  --res_backward_subs_resolution          true
% 2.69/1.00  --res_orphan_elimination                true
% 2.69/1.00  --res_time_limit                        2.
% 2.69/1.00  --res_out_proof                         true
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Options
% 2.69/1.00  
% 2.69/1.00  --superposition_flag                    true
% 2.69/1.00  --sup_passive_queue_type                priority_queues
% 2.69/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.00  --demod_completeness_check              fast
% 2.69/1.00  --demod_use_ground                      true
% 2.69/1.00  --sup_to_prop_solver                    passive
% 2.69/1.00  --sup_prop_simpl_new                    true
% 2.69/1.00  --sup_prop_simpl_given                  true
% 2.69/1.00  --sup_fun_splitting                     false
% 2.69/1.00  --sup_smt_interval                      50000
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Simplification Setup
% 2.69/1.00  
% 2.69/1.00  --sup_indices_passive                   []
% 2.69/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_full_bw                           [BwDemod]
% 2.69/1.00  --sup_immed_triv                        [TrivRules]
% 2.69/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_immed_bw_main                     []
% 2.69/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  
% 2.69/1.00  ------ Combination Options
% 2.69/1.00  
% 2.69/1.00  --comb_res_mult                         3
% 2.69/1.00  --comb_sup_mult                         2
% 2.69/1.00  --comb_inst_mult                        10
% 2.69/1.00  
% 2.69/1.00  ------ Debug Options
% 2.69/1.00  
% 2.69/1.00  --dbg_backtrace                         false
% 2.69/1.00  --dbg_dump_prop_clauses                 false
% 2.69/1.00  --dbg_dump_prop_clauses_file            -
% 2.69/1.00  --dbg_out_stat                          false
% 2.69/1.00  ------ Parsing...
% 2.69/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/1.00  ------ Proving...
% 2.69/1.00  ------ Problem Properties 
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  clauses                                 17
% 2.69/1.00  conjectures                             6
% 2.69/1.00  EPR                                     3
% 2.69/1.00  Horn                                    6
% 2.69/1.00  unary                                   5
% 2.69/1.00  binary                                  0
% 2.69/1.00  lits                                    70
% 2.69/1.00  lits eq                                 52
% 2.69/1.00  fd_pure                                 0
% 2.69/1.00  fd_pseudo                               0
% 2.69/1.00  fd_cond                                 4
% 2.69/1.00  fd_pseudo_cond                          4
% 2.69/1.00  AC symbols                              0
% 2.69/1.00  
% 2.69/1.00  ------ Schedule dynamic 5 is on 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  ------ 
% 2.69/1.00  Current options:
% 2.69/1.00  ------ 
% 2.69/1.00  
% 2.69/1.00  ------ Input Options
% 2.69/1.00  
% 2.69/1.00  --out_options                           all
% 2.69/1.00  --tptp_safe_out                         true
% 2.69/1.00  --problem_path                          ""
% 2.69/1.00  --include_path                          ""
% 2.69/1.00  --clausifier                            res/vclausify_rel
% 2.69/1.00  --clausifier_options                    --mode clausify
% 2.69/1.00  --stdin                                 false
% 2.69/1.00  --stats_out                             all
% 2.69/1.00  
% 2.69/1.00  ------ General Options
% 2.69/1.00  
% 2.69/1.00  --fof                                   false
% 2.69/1.00  --time_out_real                         305.
% 2.69/1.00  --time_out_virtual                      -1.
% 2.69/1.00  --symbol_type_check                     false
% 2.69/1.00  --clausify_out                          false
% 2.69/1.00  --sig_cnt_out                           false
% 2.69/1.00  --trig_cnt_out                          false
% 2.69/1.00  --trig_cnt_out_tolerance                1.
% 2.69/1.00  --trig_cnt_out_sk_spl                   false
% 2.69/1.00  --abstr_cl_out                          false
% 2.69/1.00  
% 2.69/1.00  ------ Global Options
% 2.69/1.00  
% 2.69/1.00  --schedule                              default
% 2.69/1.00  --add_important_lit                     false
% 2.69/1.00  --prop_solver_per_cl                    1000
% 2.69/1.00  --min_unsat_core                        false
% 2.69/1.00  --soft_assumptions                      false
% 2.69/1.00  --soft_lemma_size                       3
% 2.69/1.00  --prop_impl_unit_size                   0
% 2.69/1.00  --prop_impl_unit                        []
% 2.69/1.00  --share_sel_clauses                     true
% 2.69/1.00  --reset_solvers                         false
% 2.69/1.00  --bc_imp_inh                            [conj_cone]
% 2.69/1.00  --conj_cone_tolerance                   3.
% 2.69/1.00  --extra_neg_conj                        none
% 2.69/1.00  --large_theory_mode                     true
% 2.69/1.00  --prolific_symb_bound                   200
% 2.69/1.00  --lt_threshold                          2000
% 2.69/1.00  --clause_weak_htbl                      true
% 2.69/1.00  --gc_record_bc_elim                     false
% 2.69/1.00  
% 2.69/1.00  ------ Preprocessing Options
% 2.69/1.00  
% 2.69/1.00  --preprocessing_flag                    true
% 2.69/1.00  --time_out_prep_mult                    0.1
% 2.69/1.00  --splitting_mode                        input
% 2.69/1.00  --splitting_grd                         true
% 2.69/1.00  --splitting_cvd                         false
% 2.69/1.00  --splitting_cvd_svl                     false
% 2.69/1.00  --splitting_nvd                         32
% 2.69/1.00  --sub_typing                            true
% 2.69/1.00  --prep_gs_sim                           true
% 2.69/1.00  --prep_unflatten                        true
% 2.69/1.00  --prep_res_sim                          true
% 2.69/1.00  --prep_upred                            true
% 2.69/1.00  --prep_sem_filter                       exhaustive
% 2.69/1.00  --prep_sem_filter_out                   false
% 2.69/1.00  --pred_elim                             true
% 2.69/1.00  --res_sim_input                         true
% 2.69/1.00  --eq_ax_congr_red                       true
% 2.69/1.00  --pure_diseq_elim                       true
% 2.69/1.00  --brand_transform                       false
% 2.69/1.00  --non_eq_to_eq                          false
% 2.69/1.00  --prep_def_merge                        true
% 2.69/1.00  --prep_def_merge_prop_impl              false
% 2.69/1.00  --prep_def_merge_mbd                    true
% 2.69/1.00  --prep_def_merge_tr_red                 false
% 2.69/1.00  --prep_def_merge_tr_cl                  false
% 2.69/1.00  --smt_preprocessing                     true
% 2.69/1.00  --smt_ac_axioms                         fast
% 2.69/1.00  --preprocessed_out                      false
% 2.69/1.00  --preprocessed_stats                    false
% 2.69/1.00  
% 2.69/1.00  ------ Abstraction refinement Options
% 2.69/1.00  
% 2.69/1.00  --abstr_ref                             []
% 2.69/1.00  --abstr_ref_prep                        false
% 2.69/1.00  --abstr_ref_until_sat                   false
% 2.69/1.00  --abstr_ref_sig_restrict                funpre
% 2.69/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.00  --abstr_ref_under                       []
% 2.69/1.00  
% 2.69/1.00  ------ SAT Options
% 2.69/1.00  
% 2.69/1.00  --sat_mode                              false
% 2.69/1.00  --sat_fm_restart_options                ""
% 2.69/1.00  --sat_gr_def                            false
% 2.69/1.00  --sat_epr_types                         true
% 2.69/1.00  --sat_non_cyclic_types                  false
% 2.69/1.00  --sat_finite_models                     false
% 2.69/1.00  --sat_fm_lemmas                         false
% 2.69/1.00  --sat_fm_prep                           false
% 2.69/1.00  --sat_fm_uc_incr                        true
% 2.69/1.00  --sat_out_model                         small
% 2.69/1.00  --sat_out_clauses                       false
% 2.69/1.00  
% 2.69/1.00  ------ QBF Options
% 2.69/1.00  
% 2.69/1.00  --qbf_mode                              false
% 2.69/1.00  --qbf_elim_univ                         false
% 2.69/1.00  --qbf_dom_inst                          none
% 2.69/1.00  --qbf_dom_pre_inst                      false
% 2.69/1.00  --qbf_sk_in                             false
% 2.69/1.00  --qbf_pred_elim                         true
% 2.69/1.00  --qbf_split                             512
% 2.69/1.00  
% 2.69/1.00  ------ BMC1 Options
% 2.69/1.00  
% 2.69/1.00  --bmc1_incremental                      false
% 2.69/1.00  --bmc1_axioms                           reachable_all
% 2.69/1.00  --bmc1_min_bound                        0
% 2.69/1.00  --bmc1_max_bound                        -1
% 2.69/1.00  --bmc1_max_bound_default                -1
% 2.69/1.00  --bmc1_symbol_reachability              true
% 2.69/1.00  --bmc1_property_lemmas                  false
% 2.69/1.00  --bmc1_k_induction                      false
% 2.69/1.00  --bmc1_non_equiv_states                 false
% 2.69/1.00  --bmc1_deadlock                         false
% 2.69/1.00  --bmc1_ucm                              false
% 2.69/1.00  --bmc1_add_unsat_core                   none
% 2.69/1.00  --bmc1_unsat_core_children              false
% 2.69/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.00  --bmc1_out_stat                         full
% 2.69/1.00  --bmc1_ground_init                      false
% 2.69/1.00  --bmc1_pre_inst_next_state              false
% 2.69/1.00  --bmc1_pre_inst_state                   false
% 2.69/1.00  --bmc1_pre_inst_reach_state             false
% 2.69/1.00  --bmc1_out_unsat_core                   false
% 2.69/1.00  --bmc1_aig_witness_out                  false
% 2.69/1.00  --bmc1_verbose                          false
% 2.69/1.00  --bmc1_dump_clauses_tptp                false
% 2.69/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.00  --bmc1_dump_file                        -
% 2.69/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.00  --bmc1_ucm_extend_mode                  1
% 2.69/1.00  --bmc1_ucm_init_mode                    2
% 2.69/1.00  --bmc1_ucm_cone_mode                    none
% 2.69/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.00  --bmc1_ucm_relax_model                  4
% 2.69/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.00  --bmc1_ucm_layered_model                none
% 2.69/1.00  --bmc1_ucm_max_lemma_size               10
% 2.69/1.00  
% 2.69/1.00  ------ AIG Options
% 2.69/1.00  
% 2.69/1.00  --aig_mode                              false
% 2.69/1.00  
% 2.69/1.00  ------ Instantiation Options
% 2.69/1.00  
% 2.69/1.00  --instantiation_flag                    true
% 2.69/1.00  --inst_sos_flag                         false
% 2.69/1.00  --inst_sos_phase                        true
% 2.69/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.00  --inst_lit_sel_side                     none
% 2.69/1.00  --inst_solver_per_active                1400
% 2.69/1.00  --inst_solver_calls_frac                1.
% 2.69/1.00  --inst_passive_queue_type               priority_queues
% 2.69/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.00  --inst_passive_queues_freq              [25;2]
% 2.69/1.00  --inst_dismatching                      true
% 2.69/1.00  --inst_eager_unprocessed_to_passive     true
% 2.69/1.00  --inst_prop_sim_given                   true
% 2.69/1.00  --inst_prop_sim_new                     false
% 2.69/1.00  --inst_subs_new                         false
% 2.69/1.00  --inst_eq_res_simp                      false
% 2.69/1.00  --inst_subs_given                       false
% 2.69/1.00  --inst_orphan_elimination               true
% 2.69/1.00  --inst_learning_loop_flag               true
% 2.69/1.00  --inst_learning_start                   3000
% 2.69/1.00  --inst_learning_factor                  2
% 2.69/1.00  --inst_start_prop_sim_after_learn       3
% 2.69/1.00  --inst_sel_renew                        solver
% 2.69/1.00  --inst_lit_activity_flag                true
% 2.69/1.00  --inst_restr_to_given                   false
% 2.69/1.00  --inst_activity_threshold               500
% 2.69/1.00  --inst_out_proof                        true
% 2.69/1.00  
% 2.69/1.00  ------ Resolution Options
% 2.69/1.00  
% 2.69/1.00  --resolution_flag                       false
% 2.69/1.00  --res_lit_sel                           adaptive
% 2.69/1.00  --res_lit_sel_side                      none
% 2.69/1.00  --res_ordering                          kbo
% 2.69/1.00  --res_to_prop_solver                    active
% 2.69/1.00  --res_prop_simpl_new                    false
% 2.69/1.00  --res_prop_simpl_given                  true
% 2.69/1.00  --res_passive_queue_type                priority_queues
% 2.69/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.00  --res_passive_queues_freq               [15;5]
% 2.69/1.00  --res_forward_subs                      full
% 2.69/1.00  --res_backward_subs                     full
% 2.69/1.00  --res_forward_subs_resolution           true
% 2.69/1.00  --res_backward_subs_resolution          true
% 2.69/1.00  --res_orphan_elimination                true
% 2.69/1.00  --res_time_limit                        2.
% 2.69/1.00  --res_out_proof                         true
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Options
% 2.69/1.00  
% 2.69/1.00  --superposition_flag                    true
% 2.69/1.00  --sup_passive_queue_type                priority_queues
% 2.69/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.00  --demod_completeness_check              fast
% 2.69/1.00  --demod_use_ground                      true
% 2.69/1.00  --sup_to_prop_solver                    passive
% 2.69/1.00  --sup_prop_simpl_new                    true
% 2.69/1.00  --sup_prop_simpl_given                  true
% 2.69/1.00  --sup_fun_splitting                     false
% 2.69/1.00  --sup_smt_interval                      50000
% 2.69/1.00  
% 2.69/1.00  ------ Superposition Simplification Setup
% 2.69/1.00  
% 2.69/1.00  --sup_indices_passive                   []
% 2.69/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_full_bw                           [BwDemod]
% 2.69/1.00  --sup_immed_triv                        [TrivRules]
% 2.69/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_immed_bw_main                     []
% 2.69/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.00  
% 2.69/1.00  ------ Combination Options
% 2.69/1.00  
% 2.69/1.00  --comb_res_mult                         3
% 2.69/1.00  --comb_sup_mult                         2
% 2.69/1.00  --comb_inst_mult                        10
% 2.69/1.00  
% 2.69/1.00  ------ Debug Options
% 2.69/1.00  
% 2.69/1.00  --dbg_backtrace                         false
% 2.69/1.00  --dbg_dump_prop_clauses                 false
% 2.69/1.00  --dbg_dump_prop_clauses_file            -
% 2.69/1.00  --dbg_out_stat                          false
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  ------ Proving...
% 2.69/1.00  
% 2.69/1.00  
% 2.69/1.00  % SZS status Theorem for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00   Resolution empty clause
% 2.69/1.00  
% 2.69/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/1.00  
% 2.69/1.00  fof(f5,axiom,(
% 2.69/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f11,plain,(
% 2.69/1.00    ! [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X5] : (? [X6] : (? [X7] : ((X3 != X5 & k3_mcart_1(X5,X6,X7) = X4) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0))) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.69/1.00    inference(ennf_transformation,[],[f5])).
% 2.69/1.00  
% 2.69/1.00  fof(f12,plain,(
% 2.69/1.00    ! [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X5] : (? [X6] : (? [X7] : (X3 != X5 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.69/1.00    inference(flattening,[],[f11])).
% 2.69/1.00  
% 2.69/1.00  fof(f17,plain,(
% 2.69/1.00    ( ! [X6,X5] : (! [X4,X3,X2,X1,X0] : (? [X7] : (X3 != X5 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) => (X3 != X5 & k3_mcart_1(X5,X6,sK2(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)))) )),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f16,plain,(
% 2.69/1.00    ( ! [X5] : (! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (X3 != X5 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (X3 != X5 & k3_mcart_1(X5,sK1(X0,X1,X2,X3,X4),X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)))) )),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f15,plain,(
% 2.69/1.00    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (X3 != X5 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (sK0(X0,X1,X2,X3,X4) != X3 & k3_mcart_1(sK0(X0,X1,X2,X3,X4),X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)))),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f18,plain,(
% 2.69/1.00    ! [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | (((sK0(X0,X1,X2,X3,X4) != X3 & k3_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f17,f16,f15])).
% 2.69/1.00  
% 2.69/1.00  fof(f29,plain,(
% 2.69/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f18])).
% 2.69/1.00  
% 2.69/1.00  fof(f2,axiom,(
% 2.69/1.00    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f22,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f2])).
% 2.69/1.00  
% 2.69/1.00  fof(f50,plain,(
% 2.69/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.69/1.00    inference(definition_unfolding,[],[f29,f22])).
% 2.69/1.00  
% 2.69/1.00  fof(f30,plain,(
% 2.69/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f18])).
% 2.69/1.00  
% 2.69/1.00  fof(f49,plain,(
% 2.69/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.69/1.00    inference(definition_unfolding,[],[f30,f22])).
% 2.69/1.00  
% 2.69/1.00  fof(f31,plain,(
% 2.69/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f18])).
% 2.69/1.00  
% 2.69/1.00  fof(f48,plain,(
% 2.69/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.69/1.00    inference(definition_unfolding,[],[f31,f22])).
% 2.69/1.00  
% 2.69/1.00  fof(f6,conjecture,(
% 2.69/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f7,negated_conjecture,(
% 2.69/1.00    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.69/1.00    inference(negated_conjecture,[],[f6])).
% 2.69/1.00  
% 2.69/1.00  fof(f13,plain,(
% 2.69/1.00    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.69/1.00    inference(ennf_transformation,[],[f7])).
% 2.69/1.00  
% 2.69/1.00  fof(f14,plain,(
% 2.69/1.00    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.69/1.00    inference(flattening,[],[f13])).
% 2.69/1.00  
% 2.69/1.00  fof(f19,plain,(
% 2.69/1.00    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k6_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X6 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 2.69/1.00    introduced(choice_axiom,[])).
% 2.69/1.00  
% 2.69/1.00  fof(f20,plain,(
% 2.69/1.00    k6_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X6 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f14,f19])).
% 2.69/1.00  
% 2.69/1.00  fof(f34,plain,(
% 2.69/1.00    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.69/1.00    inference(cnf_transformation,[],[f20])).
% 2.69/1.00  
% 2.69/1.00  fof(f52,plain,(
% 2.69/1.00    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.69/1.00    inference(definition_unfolding,[],[f34,f22])).
% 2.69/1.00  
% 2.69/1.00  fof(f32,plain,(
% 2.69/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f18])).
% 2.69/1.00  
% 2.69/1.00  fof(f1,axiom,(
% 2.69/1.00    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f21,plain,(
% 2.69/1.00    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f1])).
% 2.69/1.00  
% 2.69/1.00  fof(f47,plain,(
% 2.69/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.69/1.00    inference(definition_unfolding,[],[f32,f21,f22])).
% 2.69/1.00  
% 2.69/1.00  fof(f3,axiom,(
% 2.69/1.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f8,plain,(
% 2.69/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.69/1.00    inference(ennf_transformation,[],[f3])).
% 2.69/1.00  
% 2.69/1.00  fof(f23,plain,(
% 2.69/1.00    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.69/1.00    inference(cnf_transformation,[],[f8])).
% 2.69/1.00  
% 2.69/1.00  fof(f42,plain,(
% 2.69/1.00    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.69/1.00    inference(definition_unfolding,[],[f23,f22])).
% 2.69/1.00  
% 2.69/1.00  fof(f36,plain,(
% 2.69/1.00    k1_xboole_0 != sK3),
% 2.69/1.00    inference(cnf_transformation,[],[f20])).
% 2.69/1.00  
% 2.69/1.00  fof(f37,plain,(
% 2.69/1.00    k1_xboole_0 != sK4),
% 2.69/1.00    inference(cnf_transformation,[],[f20])).
% 2.69/1.00  
% 2.69/1.00  fof(f38,plain,(
% 2.69/1.00    k1_xboole_0 != sK5),
% 2.69/1.00    inference(cnf_transformation,[],[f20])).
% 2.69/1.00  
% 2.69/1.00  fof(f35,plain,(
% 2.69/1.00    ( ! [X6,X7,X5] : (sK6 = X6 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.69/1.00    inference(cnf_transformation,[],[f20])).
% 2.69/1.00  
% 2.69/1.00  fof(f51,plain,(
% 2.69/1.00    ( ! [X6,X7,X5] : (sK6 = X6 | k4_tarski(k4_tarski(X5,X6),X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.69/1.00    inference(definition_unfolding,[],[f35,f21])).
% 2.69/1.00  
% 2.69/1.00  fof(f24,plain,(
% 2.69/1.00    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.69/1.00    inference(cnf_transformation,[],[f8])).
% 2.69/1.00  
% 2.69/1.00  fof(f41,plain,(
% 2.69/1.00    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.69/1.00    inference(definition_unfolding,[],[f24,f22])).
% 2.69/1.00  
% 2.69/1.00  fof(f39,plain,(
% 2.69/1.00    k6_mcart_1(sK3,sK4,sK5,sK7) != sK6),
% 2.69/1.00    inference(cnf_transformation,[],[f20])).
% 2.69/1.00  
% 2.69/1.00  fof(f4,axiom,(
% 2.69/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 2.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.00  
% 2.69/1.00  fof(f9,plain,(
% 2.69/1.00    ! [X0,X1,X2,X3] : ((! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 2.69/1.00    inference(ennf_transformation,[],[f4])).
% 2.69/1.00  
% 2.69/1.00  fof(f10,plain,(
% 2.69/1.00    ! [X0,X1,X2,X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 2.69/1.00    inference(flattening,[],[f9])).
% 2.69/1.00  
% 2.69/1.00  fof(f27,plain,(
% 2.69/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k3_mcart_1(X4,X5,X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 2.69/1.00    inference(cnf_transformation,[],[f10])).
% 2.69/1.00  
% 2.69/1.00  fof(f44,plain,(
% 2.69/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.69/1.00    inference(definition_unfolding,[],[f27,f21,f22])).
% 2.69/1.00  
% 2.69/1.00  fof(f54,plain,(
% 2.69/1.00    ( ! [X6,X4,X2,X0,X5,X1] : (k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.69/1.00    inference(equality_resolution,[],[f44])).
% 2.69/1.00  
% 2.69/1.00  cnf(c_10,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.69/1.00      | m1_subset_1(sK0(X1,X2,X3,X4,X0),X1)
% 2.69/1.00      | k5_mcart_1(X1,X2,X3,X0) = X4
% 2.69/1.00      | k1_xboole_0 = X3
% 2.69/1.00      | k1_xboole_0 = X2
% 2.69/1.00      | k1_xboole_0 = X1 ),
% 2.69/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_374,plain,
% 2.69/1.00      ( k5_mcart_1(X0,X1,X2,X3) = X4
% 2.69/1.00      | k1_xboole_0 = X2
% 2.69/1.00      | k1_xboole_0 = X1
% 2.69/1.00      | k1_xboole_0 = X0
% 2.69/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
% 2.69/1.00      | m1_subset_1(sK0(X0,X1,X2,X4,X3),X0) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_9,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.69/1.00      | m1_subset_1(sK1(X1,X2,X3,X4,X0),X2)
% 2.69/1.00      | k5_mcart_1(X1,X2,X3,X0) = X4
% 2.69/1.00      | k1_xboole_0 = X3
% 2.69/1.00      | k1_xboole_0 = X2
% 2.69/1.00      | k1_xboole_0 = X1 ),
% 2.69/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_375,plain,
% 2.69/1.00      ( k5_mcart_1(X0,X1,X2,X3) = X4
% 2.69/1.00      | k1_xboole_0 = X2
% 2.69/1.00      | k1_xboole_0 = X1
% 2.69/1.00      | k1_xboole_0 = X0
% 2.69/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
% 2.69/1.00      | m1_subset_1(sK1(X0,X1,X2,X4,X3),X1) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_8,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.69/1.00      | m1_subset_1(sK2(X1,X2,X3,X4,X0),X3)
% 2.69/1.00      | k5_mcart_1(X1,X2,X3,X0) = X4
% 2.69/1.00      | k1_xboole_0 = X3
% 2.69/1.00      | k1_xboole_0 = X2
% 2.69/1.00      | k1_xboole_0 = X1 ),
% 2.69/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_376,plain,
% 2.69/1.00      ( k5_mcart_1(X0,X1,X2,X3) = X4
% 2.69/1.00      | k1_xboole_0 = X2
% 2.69/1.00      | k1_xboole_0 = X1
% 2.69/1.00      | k1_xboole_0 = X0
% 2.69/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top
% 2.69/1.00      | m1_subset_1(sK2(X0,X1,X2,X4,X3),X2) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_16,negated_conjecture,
% 2.69/1.00      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 2.69/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_372,plain,
% 2.69/1.00      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_7,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.69/1.00      | k5_mcart_1(X1,X2,X3,X0) = X4
% 2.69/1.00      | k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X0),sK1(X1,X2,X3,X4,X0)),sK2(X1,X2,X3,X4,X0)) = X0
% 2.69/1.00      | k1_xboole_0 = X3
% 2.69/1.00      | k1_xboole_0 = X2
% 2.69/1.00      | k1_xboole_0 = X1 ),
% 2.69/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_377,plain,
% 2.69/1.00      ( k5_mcart_1(X0,X1,X2,X3) = X4
% 2.69/1.00      | k4_tarski(k4_tarski(sK0(X0,X1,X2,X4,X3),sK1(X0,X1,X2,X4,X3)),sK2(X0,X1,X2,X4,X3)) = X3
% 2.69/1.00      | k1_xboole_0 = X2
% 2.69/1.00      | k1_xboole_0 = X1
% 2.69/1.00      | k1_xboole_0 = X0
% 2.69/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.69/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_1994,plain,
% 2.69/1.00      ( k5_mcart_1(sK3,sK4,sK5,sK7) = X0
% 2.69/1.00      | k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
% 2.69/1.00      | sK5 = k1_xboole_0
% 2.69/1.00      | sK4 = k1_xboole_0
% 2.69/1.00      | sK3 = k1_xboole_0 ),
% 2.69/1.00      inference(superposition,[status(thm)],[c_372,c_377]) ).
% 2.69/1.00  
% 2.69/1.00  cnf(c_2,plain,
% 2.69/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.69/1.01      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.69/1.01      | k1_xboole_0 = X3
% 2.69/1.01      | k1_xboole_0 = X2
% 2.69/1.01      | k1_xboole_0 = X1 ),
% 2.69/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_382,plain,
% 2.69/1.01      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.69/1.01      | k1_xboole_0 = X2
% 2.69/1.01      | k1_xboole_0 = X1
% 2.69/1.01      | k1_xboole_0 = X0
% 2.69/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.69/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_1057,plain,
% 2.69/1.01      ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 2.69/1.01      | sK5 = k1_xboole_0
% 2.69/1.01      | sK4 = k1_xboole_0
% 2.69/1.01      | sK3 = k1_xboole_0 ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_372,c_382]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_14,negated_conjecture,
% 2.69/1.01      ( k1_xboole_0 != sK3 ),
% 2.69/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_13,negated_conjecture,
% 2.69/1.01      ( k1_xboole_0 != sK4 ),
% 2.69/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_12,negated_conjecture,
% 2.69/1.01      ( k1_xboole_0 != sK5 ),
% 2.69/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_157,plain,( X0 = X0 ),theory(equality) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_176,plain,
% 2.69/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 2.69/1.01      inference(instantiation,[status(thm)],[c_157]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_158,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_554,plain,
% 2.69/1.01      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.69/1.01      inference(instantiation,[status(thm)],[c_158]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_555,plain,
% 2.69/1.01      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 2.69/1.01      inference(instantiation,[status(thm)],[c_554]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_556,plain,
% 2.69/1.01      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.69/1.01      inference(instantiation,[status(thm)],[c_158]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_557,plain,
% 2.69/1.01      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.69/1.01      inference(instantiation,[status(thm)],[c_556]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_558,plain,
% 2.69/1.01      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.69/1.01      inference(instantiation,[status(thm)],[c_158]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_559,plain,
% 2.69/1.01      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.69/1.01      inference(instantiation,[status(thm)],[c_558]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_1461,plain,
% 2.69/1.01      ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
% 2.69/1.01      inference(global_propositional_subsumption,
% 2.69/1.01                [status(thm)],
% 2.69/1.01                [c_1057,c_14,c_13,c_12,c_176,c_555,c_557,c_559]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2063,plain,
% 2.69/1.01      ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | sK5 = k1_xboole_0
% 2.69/1.01      | sK4 = k1_xboole_0
% 2.69/1.01      | sK3 = k1_xboole_0 ),
% 2.69/1.01      inference(demodulation,[status(thm)],[c_1994,c_1461]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2568,plain,
% 2.69/1.01      ( k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7 ),
% 2.69/1.01      inference(global_propositional_subsumption,
% 2.69/1.01                [status(thm)],
% 2.69/1.01                [c_2063,c_14,c_13,c_12,c_176,c_555,c_557,c_559]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2569,plain,
% 2.69/1.01      ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK1(sK3,sK4,sK5,X0,sK7)),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.69/1.01      inference(renaming,[status(thm)],[c_2568]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_15,negated_conjecture,
% 2.69/1.01      ( ~ m1_subset_1(X0,sK5)
% 2.69/1.01      | ~ m1_subset_1(X1,sK4)
% 2.69/1.01      | ~ m1_subset_1(X2,sK3)
% 2.69/1.01      | k4_tarski(k4_tarski(X2,X1),X0) != sK7
% 2.69/1.01      | sK6 = X1 ),
% 2.69/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_373,plain,
% 2.69/1.01      ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
% 2.69/1.01      | sK6 = X1
% 2.69/1.01      | m1_subset_1(X2,sK5) != iProver_top
% 2.69/1.01      | m1_subset_1(X1,sK4) != iProver_top
% 2.69/1.01      | m1_subset_1(X0,sK3) != iProver_top ),
% 2.69/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2574,plain,
% 2.69/1.01      ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | m1_subset_1(sK2(sK3,sK4,sK5,X0,sK7),sK5) != iProver_top
% 2.69/1.01      | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
% 2.69/1.01      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_2569,c_373]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2693,plain,
% 2.69/1.01      ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | sK5 = k1_xboole_0
% 2.69/1.01      | sK4 = k1_xboole_0
% 2.69/1.01      | sK3 = k1_xboole_0
% 2.69/1.01      | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
% 2.69/1.01      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.69/1.01      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_376,c_2574]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2694,plain,
% 2.69/1.01      ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | sK5 = k1_xboole_0
% 2.69/1.01      | sK4 = k1_xboole_0
% 2.69/1.01      | sK3 = k1_xboole_0
% 2.69/1.01      | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
% 2.69/1.01      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.69/1.01      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.69/1.01      inference(demodulation,[status(thm)],[c_2693,c_1461]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_17,plain,
% 2.69/1.01      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 2.69/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2709,plain,
% 2.69/1.01      ( m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.69/1.01      | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
% 2.69/1.01      | sK1(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.69/1.01      inference(global_propositional_subsumption,
% 2.69/1.01                [status(thm)],
% 2.69/1.01                [c_2694,c_17,c_14,c_13,c_12,c_176,c_555,c_557,c_559]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2710,plain,
% 2.69/1.01      ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | m1_subset_1(sK1(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
% 2.69/1.01      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
% 2.69/1.01      inference(renaming,[status(thm)],[c_2709]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2719,plain,
% 2.69/1.01      ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | sK5 = k1_xboole_0
% 2.69/1.01      | sK4 = k1_xboole_0
% 2.69/1.01      | sK3 = k1_xboole_0
% 2.69/1.01      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.69/1.01      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_375,c_2710]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2720,plain,
% 2.69/1.01      ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | sK5 = k1_xboole_0
% 2.69/1.01      | sK4 = k1_xboole_0
% 2.69/1.01      | sK3 = k1_xboole_0
% 2.69/1.01      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.69/1.01      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.69/1.01      inference(demodulation,[status(thm)],[c_2719,c_1461]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2725,plain,
% 2.69/1.01      ( m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top
% 2.69/1.01      | sK1(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.69/1.01      inference(global_propositional_subsumption,
% 2.69/1.01                [status(thm)],
% 2.69/1.01                [c_2720,c_17,c_14,c_13,c_12,c_176,c_555,c_557,c_559]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2726,plain,
% 2.69/1.01      ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | m1_subset_1(sK0(sK3,sK4,sK5,X0,sK7),sK3) != iProver_top ),
% 2.69/1.01      inference(renaming,[status(thm)],[c_2725]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2734,plain,
% 2.69/1.01      ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k5_mcart_1(sK3,sK4,sK5,sK7) = X0
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | sK5 = k1_xboole_0
% 2.69/1.01      | sK4 = k1_xboole_0
% 2.69/1.01      | sK3 = k1_xboole_0
% 2.69/1.01      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_374,c_2726]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2735,plain,
% 2.69/1.01      ( sK1(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | sK5 = k1_xboole_0
% 2.69/1.01      | sK4 = k1_xboole_0
% 2.69/1.01      | sK3 = k1_xboole_0
% 2.69/1.01      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) != iProver_top ),
% 2.69/1.01      inference(demodulation,[status(thm)],[c_2734,c_1461]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2740,plain,
% 2.69/1.01      ( sK1(sK3,sK4,sK5,X0,sK7) = sK6 | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.69/1.01      inference(global_propositional_subsumption,
% 2.69/1.01                [status(thm)],
% 2.69/1.01                [c_2735,c_17,c_14,c_13,c_12,c_176,c_555,c_557,c_559]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2746,plain,
% 2.69/1.01      ( k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK6),sK2(sK3,sK4,sK5,X0,sK7)) = sK7
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_2740,c_2569]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2802,plain,
% 2.69/1.01      ( sK2(sK3,sK4,sK5,X0,sK7) = sK6
% 2.69/1.01      | k4_tarski(sK7,X1) != sK7
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | m1_subset_1(X1,sK5) != iProver_top
% 2.69/1.01      | m1_subset_1(sK2(sK3,sK4,sK5,X0,sK7),sK4) != iProver_top
% 2.69/1.01      | m1_subset_1(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK6),sK3) != iProver_top ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_2746,c_373]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_1,plain,
% 2.69/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.69/1.01      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.69/1.01      | k1_xboole_0 = X3
% 2.69/1.01      | k1_xboole_0 = X2
% 2.69/1.01      | k1_xboole_0 = X1 ),
% 2.69/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_383,plain,
% 2.69/1.01      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.69/1.01      | k1_xboole_0 = X2
% 2.69/1.01      | k1_xboole_0 = X1
% 2.69/1.01      | k1_xboole_0 = X0
% 2.69/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.69/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_1250,plain,
% 2.69/1.01      ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.69/1.01      | sK5 = k1_xboole_0
% 2.69/1.01      | sK4 = k1_xboole_0
% 2.69/1.01      | sK3 = k1_xboole_0 ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_372,c_383]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_1628,plain,
% 2.69/1.01      ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
% 2.69/1.01      inference(global_propositional_subsumption,
% 2.69/1.01                [status(thm)],
% 2.69/1.01                [c_1250,c_14,c_13,c_12,c_176,c_555,c_557,c_559]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_11,negated_conjecture,
% 2.69/1.01      ( k6_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
% 2.69/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_1631,plain,
% 2.69/1.01      ( k2_mcart_1(k1_mcart_1(sK7)) != sK6 ),
% 2.69/1.01      inference(demodulation,[status(thm)],[c_1628,c_11]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_4,plain,
% 2.69/1.01      ( ~ m1_subset_1(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
% 2.69/1.01      | k6_mcart_1(X3,X4,X5,k4_tarski(k4_tarski(X0,X1),X2)) = X1
% 2.69/1.01      | k1_xboole_0 = X5
% 2.69/1.01      | k1_xboole_0 = X4
% 2.69/1.01      | k1_xboole_0 = X3 ),
% 2.69/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_380,plain,
% 2.69/1.01      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X3,X4),X5)) = X4
% 2.69/1.01      | k1_xboole_0 = X0
% 2.69/1.01      | k1_xboole_0 = X2
% 2.69/1.01      | k1_xboole_0 = X1
% 2.69/1.01      | m1_subset_1(k4_tarski(k4_tarski(X3,X4),X5),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.69/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_2808,plain,
% 2.69/1.01      ( k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X3,sK7),sK6),sK2(sK3,sK4,sK5,X3,sK7))) = sK6
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X3
% 2.69/1.01      | k1_xboole_0 = X2
% 2.69/1.01      | k1_xboole_0 = X1
% 2.69/1.01      | k1_xboole_0 = X0
% 2.69/1.01      | m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_2746,c_380]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_3004,plain,
% 2.69/1.01      ( k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK6),sK2(sK3,sK4,sK5,X0,sK7))) = sK6
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | sK5 = k1_xboole_0
% 2.69/1.01      | sK4 = k1_xboole_0
% 2.69/1.01      | sK3 = k1_xboole_0 ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_372,c_2808]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_3028,plain,
% 2.69/1.01      ( k1_mcart_1(k1_mcart_1(sK7)) = X0
% 2.69/1.01      | k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK6),sK2(sK3,sK4,sK5,X0,sK7))) = sK6 ),
% 2.69/1.01      inference(global_propositional_subsumption,
% 2.69/1.01                [status(thm)],
% 2.69/1.01                [c_3004,c_14,c_13,c_12,c_176,c_555,c_557,c_559]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_3029,plain,
% 2.69/1.01      ( k6_mcart_1(sK3,sK4,sK5,k4_tarski(k4_tarski(sK0(sK3,sK4,sK5,X0,sK7),sK6),sK2(sK3,sK4,sK5,X0,sK7))) = sK6
% 2.69/1.01      | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.69/1.01      inference(renaming,[status(thm)],[c_3028]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_3033,plain,
% 2.69/1.01      ( k6_mcart_1(sK3,sK4,sK5,sK7) = sK6 | k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_2746,c_3029]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_3034,plain,
% 2.69/1.01      ( k1_mcart_1(k1_mcart_1(sK7)) = X0 | k2_mcart_1(k1_mcart_1(sK7)) = sK6 ),
% 2.69/1.01      inference(demodulation,[status(thm)],[c_3033,c_1628]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_3037,plain,
% 2.69/1.01      ( k1_mcart_1(k1_mcart_1(sK7)) = X0 ),
% 2.69/1.01      inference(global_propositional_subsumption,
% 2.69/1.01                [status(thm)],
% 2.69/1.01                [c_2802,c_1631,c_3034]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_3286,plain,
% 2.69/1.01      ( X0 = X1 ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_3037,c_3037]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_3551,plain,
% 2.69/1.01      ( k1_xboole_0 != X0 ),
% 2.69/1.01      inference(superposition,[status(thm)],[c_3286,c_14]) ).
% 2.69/1.01  
% 2.69/1.01  cnf(c_3553,plain,
% 2.69/1.01      ( $false ),
% 2.69/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3551,c_3286]) ).
% 2.69/1.01  
% 2.69/1.01  
% 2.69/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/1.01  
% 2.69/1.01  ------                               Statistics
% 2.69/1.01  
% 2.69/1.01  ------ General
% 2.69/1.01  
% 2.69/1.01  abstr_ref_over_cycles:                  0
% 2.69/1.01  abstr_ref_under_cycles:                 0
% 2.69/1.01  gc_basic_clause_elim:                   0
% 2.69/1.01  forced_gc_time:                         0
% 2.69/1.01  parsing_time:                           0.009
% 2.69/1.01  unif_index_cands_time:                  0.
% 2.69/1.01  unif_index_add_time:                    0.
% 2.69/1.01  orderings_time:                         0.
% 2.69/1.01  out_proof_time:                         0.008
% 2.69/1.01  total_time:                             0.158
% 2.69/1.01  num_of_symbols:                         48
% 2.69/1.01  num_of_terms:                           5416
% 2.69/1.01  
% 2.69/1.01  ------ Preprocessing
% 2.69/1.01  
% 2.69/1.01  num_of_splits:                          0
% 2.69/1.01  num_of_split_atoms:                     0
% 2.69/1.01  num_of_reused_defs:                     0
% 2.69/1.01  num_eq_ax_congr_red:                    42
% 2.69/1.01  num_of_sem_filtered_clauses:            1
% 2.69/1.01  num_of_subtypes:                        0
% 2.69/1.01  monotx_restored_types:                  0
% 2.69/1.01  sat_num_of_epr_types:                   0
% 2.69/1.01  sat_num_of_non_cyclic_types:            0
% 2.69/1.01  sat_guarded_non_collapsed_types:        0
% 2.69/1.01  num_pure_diseq_elim:                    0
% 2.69/1.01  simp_replaced_by:                       0
% 2.69/1.01  res_preprocessed:                       72
% 2.69/1.01  prep_upred:                             0
% 2.69/1.01  prep_unflattend:                        0
% 2.69/1.01  smt_new_axioms:                         0
% 2.69/1.01  pred_elim_cands:                        1
% 2.69/1.01  pred_elim:                              0
% 2.69/1.01  pred_elim_cl:                           0
% 2.69/1.01  pred_elim_cycles:                       1
% 2.69/1.01  merged_defs:                            0
% 2.69/1.01  merged_defs_ncl:                        0
% 2.69/1.01  bin_hyper_res:                          0
% 2.69/1.01  prep_cycles:                            3
% 2.69/1.01  pred_elim_time:                         0.
% 2.69/1.01  splitting_time:                         0.
% 2.69/1.01  sem_filter_time:                        0.
% 2.69/1.01  monotx_time:                            0.
% 2.69/1.01  subtype_inf_time:                       0.
% 2.69/1.01  
% 2.69/1.01  ------ Problem properties
% 2.69/1.01  
% 2.69/1.01  clauses:                                17
% 2.69/1.01  conjectures:                            6
% 2.69/1.01  epr:                                    3
% 2.69/1.01  horn:                                   6
% 2.69/1.01  ground:                                 5
% 2.69/1.01  unary:                                  5
% 2.69/1.01  binary:                                 0
% 2.69/1.01  lits:                                   70
% 2.69/1.01  lits_eq:                                52
% 2.69/1.01  fd_pure:                                0
% 2.69/1.01  fd_pseudo:                              0
% 2.69/1.01  fd_cond:                                4
% 2.69/1.01  fd_pseudo_cond:                         4
% 2.69/1.01  ac_symbols:                             0
% 2.69/1.01  
% 2.69/1.01  ------ Propositional Solver
% 2.69/1.01  
% 2.69/1.01  prop_solver_calls:                      21
% 2.69/1.01  prop_fast_solver_calls:                 755
% 2.69/1.01  smt_solver_calls:                       0
% 2.69/1.01  smt_fast_solver_calls:                  0
% 2.69/1.01  prop_num_of_clauses:                    1064
% 2.69/1.01  prop_preprocess_simplified:             3929
% 2.69/1.01  prop_fo_subsumed:                       36
% 2.69/1.01  prop_solver_time:                       0.
% 2.69/1.01  smt_solver_time:                        0.
% 2.69/1.01  smt_fast_solver_time:                   0.
% 2.69/1.01  prop_fast_solver_time:                  0.
% 2.69/1.01  prop_unsat_core_time:                   0.
% 2.69/1.01  
% 2.69/1.01  ------ QBF
% 2.69/1.01  
% 2.69/1.01  qbf_q_res:                              0
% 2.69/1.01  qbf_num_tautologies:                    0
% 2.69/1.01  qbf_prep_cycles:                        0
% 2.69/1.01  
% 2.69/1.01  ------ BMC1
% 2.69/1.01  
% 2.69/1.01  bmc1_current_bound:                     -1
% 2.69/1.01  bmc1_last_solved_bound:                 -1
% 2.69/1.01  bmc1_unsat_core_size:                   -1
% 2.69/1.01  bmc1_unsat_core_parents_size:           -1
% 2.69/1.01  bmc1_merge_next_fun:                    0
% 2.69/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.69/1.01  
% 2.69/1.01  ------ Instantiation
% 2.69/1.01  
% 2.69/1.01  inst_num_of_clauses:                    293
% 2.69/1.01  inst_num_in_passive:                    26
% 2.69/1.01  inst_num_in_active:                     210
% 2.69/1.01  inst_num_in_unprocessed:                57
% 2.69/1.01  inst_num_of_loops:                      210
% 2.69/1.01  inst_num_of_learning_restarts:          0
% 2.69/1.01  inst_num_moves_active_passive:          0
% 2.69/1.01  inst_lit_activity:                      0
% 2.69/1.01  inst_lit_activity_moves:                0
% 2.69/1.01  inst_num_tautologies:                   0
% 2.69/1.01  inst_num_prop_implied:                  0
% 2.69/1.01  inst_num_existing_simplified:           0
% 2.69/1.01  inst_num_eq_res_simplified:             0
% 2.69/1.01  inst_num_child_elim:                    0
% 2.69/1.01  inst_num_of_dismatching_blockings:      0
% 2.69/1.01  inst_num_of_non_proper_insts:           256
% 2.69/1.01  inst_num_of_duplicates:                 0
% 2.69/1.01  inst_inst_num_from_inst_to_res:         0
% 2.69/1.01  inst_dismatching_checking_time:         0.
% 2.69/1.01  
% 2.69/1.01  ------ Resolution
% 2.69/1.01  
% 2.69/1.01  res_num_of_clauses:                     0
% 2.69/1.01  res_num_in_passive:                     0
% 2.69/1.01  res_num_in_active:                      0
% 2.69/1.01  res_num_of_loops:                       75
% 2.69/1.01  res_forward_subset_subsumed:            4
% 2.69/1.01  res_backward_subset_subsumed:           0
% 2.69/1.01  res_forward_subsumed:                   0
% 2.69/1.01  res_backward_subsumed:                  0
% 2.69/1.01  res_forward_subsumption_resolution:     0
% 2.69/1.01  res_backward_subsumption_resolution:    0
% 2.69/1.01  res_clause_to_clause_subsumption:       454
% 2.69/1.01  res_orphan_elimination:                 0
% 2.69/1.01  res_tautology_del:                      0
% 2.69/1.01  res_num_eq_res_simplified:              0
% 2.69/1.01  res_num_sel_changes:                    0
% 2.69/1.01  res_moves_from_active_to_pass:          0
% 2.69/1.01  
% 2.69/1.01  ------ Superposition
% 2.69/1.01  
% 2.69/1.01  sup_time_total:                         0.
% 2.69/1.01  sup_time_generating:                    0.
% 2.69/1.01  sup_time_sim_full:                      0.
% 2.69/1.01  sup_time_sim_immed:                     0.
% 2.69/1.01  
% 2.69/1.01  sup_num_of_clauses:                     61
% 2.69/1.01  sup_num_in_active:                      9
% 2.69/1.01  sup_num_in_passive:                     52
% 2.69/1.01  sup_num_of_loops:                       40
% 2.69/1.01  sup_fw_superposition:                   33
% 2.69/1.01  sup_bw_superposition:                   81
% 2.69/1.01  sup_immediate_simplified:               15
% 2.69/1.01  sup_given_eliminated:                   3
% 2.69/1.01  comparisons_done:                       0
% 2.69/1.01  comparisons_avoided:                    120
% 2.69/1.01  
% 2.69/1.01  ------ Simplifications
% 2.69/1.01  
% 2.69/1.01  
% 2.69/1.01  sim_fw_subset_subsumed:                 8
% 2.69/1.01  sim_bw_subset_subsumed:                 5
% 2.69/1.01  sim_fw_subsumed:                        4
% 2.69/1.01  sim_bw_subsumed:                        1
% 2.69/1.01  sim_fw_subsumption_res:                 1
% 2.69/1.01  sim_bw_subsumption_res:                 0
% 2.69/1.01  sim_tautology_del:                      0
% 2.69/1.01  sim_eq_tautology_del:                   1
% 2.69/1.01  sim_eq_res_simp:                        0
% 2.69/1.01  sim_fw_demodulated:                     6
% 2.69/1.01  sim_bw_demodulated:                     27
% 2.69/1.01  sim_light_normalised:                   0
% 2.69/1.01  sim_joinable_taut:                      0
% 2.69/1.01  sim_joinable_simp:                      0
% 2.69/1.01  sim_ac_normalised:                      0
% 2.69/1.01  sim_smt_subsumption:                    0
% 2.69/1.01  
%------------------------------------------------------------------------------
