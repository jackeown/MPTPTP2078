%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0901+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:22 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   75 (1796 expanded)
%              Number of clauses        :   34 ( 409 expanded)
%              Number of leaves         :   11 ( 552 expanded)
%              Depth                    :   18
%              Number of atoms          :  270 (11335 expanded)
%              Number of equality atoms :  254 (10024 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
                & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
                & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
                & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ~ ! [X4] :
                ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
               => ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
                  & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
                  & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
                  & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) ) )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( k2_mcart_1(X4) != k11_mcart_1(X0,X1,X2,X3,X4)
            | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(X0,X1,X2,X3,X4)
            | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(X0,X1,X2,X3,X4)
            | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(X0,X1,X2,X3,X4) )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( k2_mcart_1(X4) != k11_mcart_1(X0,X1,X2,X3,X4)
            | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(X0,X1,X2,X3,X4)
            | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(X0,X1,X2,X3,X4)
            | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(X0,X1,X2,X3,X4) )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
     => ( ( k2_mcart_1(sK8) != k11_mcart_1(X0,X1,X2,X3,sK8)
          | k2_mcart_1(k1_mcart_1(sK8)) != k10_mcart_1(X0,X1,X2,X3,sK8)
          | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k9_mcart_1(X0,X1,X2,X3,sK8)
          | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k8_mcart_1(X0,X1,X2,X3,sK8) )
        & m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( k2_mcart_1(X4) != k11_mcart_1(X0,X1,X2,X3,X4)
              | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(X0,X1,X2,X3,X4)
              | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(X0,X1,X2,X3,X4)
              | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(X0,X1,X2,X3,X4) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X4] :
          ( ( k2_mcart_1(X4) != k11_mcart_1(sK4,sK5,sK6,sK7,X4)
            | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(sK4,sK5,sK6,sK7,X4)
            | k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k9_mcart_1(sK4,sK5,sK6,sK7,X4)
            | k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) != k8_mcart_1(sK4,sK5,sK6,sK7,X4) )
          & m1_subset_1(X4,k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( k2_mcart_1(sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
      | k2_mcart_1(k1_mcart_1(sK8)) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
      | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
      | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8) )
    & m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f13,f23,f22])).

fof(f38,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK3(X0,X1) != X1
        & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f20])).

fof(f28,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f28])).

fof(f49,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_mcart_1(k4_tarski(X4,X5)) = X5
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK0(X0,X1) != X1
        & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f25,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f25])).

fof(f45,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_mcart_1(k4_tarski(X4,X5)) = X4
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f44])).

fof(f39,plain,
    ( k2_mcart_1(sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k2_mcart_1(k1_mcart_1(sK8)) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X0),k9_mcart_1(X1,X2,X3,X4,X0)),k10_mcart_1(X1,X2,X3,X4,X0)),k11_mcart_1(X1,X2,X3,X4,X0)) = X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_53,plain,
    ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK4,sK5,sK6,sK7)
    | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
    | sK8 != X4
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_8])).

cnf(c_54,plain,
    ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK4,sK5,sK6,sK7)
    | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,sK8),k9_mcart_1(X0,X1,X2,X3,sK8)),k10_mcart_1(X0,X1,X2,X3,sK8)),k11_mcart_1(X0,X1,X2,X3,sK8)) = sK8
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_53])).

cnf(c_213,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK4,sK5,sK6,sK7,sK8),k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),k10_mcart_1(sK4,sK5,sK6,sK7,sK8)),k11_mcart_1(sK4,sK5,sK6,sK7,sK8)) = sK8
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_54])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_131,plain,
    ( k4_zfmisc_1(sK4,sK5,sK6,sK7) != k4_zfmisc_1(sK4,sK5,sK6,sK7)
    | k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK4,sK5,sK6,sK7,sK8),k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),k10_mcart_1(sK4,sK5,sK6,sK7,sK8)),k11_mcart_1(sK4,sK5,sK6,sK7,sK8)) = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_94,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_147,plain,
    ( k4_zfmisc_1(sK4,sK5,sK6,sK7) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_264,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK4,sK5,sK6,sK7,sK8),k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),k10_mcart_1(sK4,sK5,sK6,sK7,sK8)),k11_mcart_1(sK4,sK5,sK6,sK7,sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_213,c_12,c_11,c_10,c_9,c_131,c_147])).

cnf(c_5,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_400,plain,
    ( k4_tarski(X0,X1) != sK8
    | k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK4,sK5,sK6,sK7,sK8),k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),k10_mcart_1(sK4,sK5,sK6,sK7,sK8)),k11_mcart_1(sK4,sK5,sK6,sK7,sK8))) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    inference(superposition,[status(thm)],[c_264,c_5])).

cnf(c_492,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | k4_tarski(X0,X1) != sK8 ),
    inference(light_normalisation,[status(thm)],[c_400,c_264])).

cnf(c_548,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8) ),
    inference(superposition,[status(thm)],[c_264,c_492])).

cnf(c_550,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK4,sK5,sK6,sK7,sK8),k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),k10_mcart_1(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(sK8)) = sK8 ),
    inference(demodulation,[status(thm)],[c_548,c_264])).

cnf(c_2,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_332,plain,
    ( k4_tarski(X0,X1) != sK8
    | k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK4,sK5,sK6,sK7,sK8),k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),k10_mcart_1(sK4,sK5,sK6,sK7,sK8)),k11_mcart_1(sK4,sK5,sK6,sK7,sK8))) = k4_tarski(k4_tarski(k8_mcart_1(sK4,sK5,sK6,sK7,sK8),k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),k10_mcart_1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(superposition,[status(thm)],[c_264,c_2])).

cnf(c_397,plain,
    ( k4_tarski(X0,X1) != sK8
    | k4_tarski(k4_tarski(k8_mcart_1(sK4,sK5,sK6,sK7,sK8),k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),k10_mcart_1(sK4,sK5,sK6,sK7,sK8)) = k1_mcart_1(sK8) ),
    inference(light_normalisation,[status(thm)],[c_332,c_264])).

cnf(c_686,plain,
    ( k4_tarski(k4_tarski(k8_mcart_1(sK4,sK5,sK6,sK7,sK8),k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),k10_mcart_1(sK4,sK5,sK6,sK7,sK8)) = k1_mcart_1(sK8) ),
    inference(superposition,[status(thm)],[c_550,c_397])).

cnf(c_334,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[status(thm)],[c_2])).

cnf(c_816,plain,
    ( k4_tarski(k8_mcart_1(sK4,sK5,sK6,sK7,sK8),k9_mcart_1(sK4,sK5,sK6,sK7,sK8)) = k1_mcart_1(k1_mcart_1(sK8)) ),
    inference(superposition,[status(thm)],[c_686,c_334])).

cnf(c_402,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[status(thm)],[c_5])).

cnf(c_1363,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(superposition,[status(thm)],[c_816,c_402])).

cnf(c_1364,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(superposition,[status(thm)],[c_816,c_334])).

cnf(c_929,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    inference(superposition,[status(thm)],[c_686,c_402])).

cnf(c_7,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k2_mcart_1(k1_mcart_1(sK8)) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k2_mcart_1(sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_551,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8))
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k2_mcart_1(sK8) != k2_mcart_1(sK8) ),
    inference(demodulation,[status(thm)],[c_548,c_7])).

cnf(c_552,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8))
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(equality_resolution_simp,[status(thm)],[c_551])).

cnf(c_1201,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k2_mcart_1(k1_mcart_1(sK8)) != k2_mcart_1(k1_mcart_1(sK8)) ),
    inference(demodulation,[status(thm)],[c_929,c_552])).

cnf(c_1202,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(equality_resolution_simp,[status(thm)],[c_1201])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1363,c_1364,c_1202])).


%------------------------------------------------------------------------------
