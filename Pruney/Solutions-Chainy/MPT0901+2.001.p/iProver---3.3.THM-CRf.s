%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:46 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  116 (3230 expanded)
%              Number of clauses        :   70 (1053 expanded)
%              Number of leaves         :   15 (1158 expanded)
%              Depth                    :   17
%              Number of atoms          :  491 (18476 expanded)
%              Number of equality atoms :  423 (15436 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ~ ! [X4] :
                ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
               => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                  & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                  & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                  & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4)
            | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4))
            | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4)
            | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4))
            | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
     => ( ( k11_mcart_1(X0,X1,X2,X3,sK8) != k2_mcart_1(sK8)
          | k10_mcart_1(X0,X1,X2,X3,sK8) != k2_mcart_1(k1_mcart_1(sK8))
          | k9_mcart_1(X0,X1,X2,X3,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
          | k8_mcart_1(X0,X1,X2,X3,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) )
        & m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4)
              | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4))
              | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
              | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X4] :
          ( ( k11_mcart_1(sK4,sK5,sK6,sK7,X4) != k2_mcart_1(X4)
            | k10_mcart_1(sK4,sK5,sK6,sK7,X4) != k2_mcart_1(k1_mcart_1(X4))
            | k9_mcart_1(sK4,sK5,sK6,sK7,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            | k8_mcart_1(sK4,sK5,sK6,sK7,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          & m1_subset_1(X4,k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(sK8)
      | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8))
      | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
      | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) )
    & m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f11,f18,f17])).

fof(f38,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f50,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) ),
    inference(definition_unfolding,[],[f38,f22])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ! [X6] :
                    ( m1_subset_1(X6,X1)
                   => ! [X7] :
                        ( m1_subset_1(X7,X2)
                       => ! [X8] :
                            ( m1_subset_1(X8,X3)
                           => k4_mcart_1(X5,X6,X7,X8) != X4 ) ) ) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( k4_mcart_1(X5,X6,X7,X8) = X4
                          & m1_subset_1(X8,X3) )
                      & m1_subset_1(X7,X2) )
                  & m1_subset_1(X6,X1) )
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X6,X7,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(X5,X6,X7,X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(X5,X6,X7,sK3(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK3(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(X5,X6,X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(X5,X6,sK2(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(X5,X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(X5,sK1(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( k4_mcart_1(X5,X6,X7,X8) = X4
                      & m1_subset_1(X8,X3) )
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( k4_mcart_1(sK0(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f15,f14,f13,f12])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f40,f22])).

fof(f34,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5,X6,X7,X8] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              | k4_mcart_1(X5,X6,X7,X8) != X4 )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f40,f22])).

fof(f51,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f46])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = X7
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f40,f22])).

fof(f52,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X7
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f47])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = X6
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f40,f22])).

fof(f53,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f48])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f40,f22])).

fof(f54,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f49])).

fof(f39,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(sK8)
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8))
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_308,plain,
    ( m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
    | k4_tarski(k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X0),sK1(X1,X2,X3,X4,X0)),sK2(X1,X2,X3,X4,X0)),sK3(X1,X2,X3,X4,X0)) = X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_317,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2246,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8)) = sK8
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_308,c_317])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_131,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_154,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_132,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_473,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_474,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_475,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_476,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_477,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_478,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_479,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_480,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_2247,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2246,c_16,c_15,c_14,c_13,c_154,c_474,c_476,c_478,c_480])).

cnf(c_10,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2250,plain,
    ( k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)) = k1_mcart_1(sK8) ),
    inference(superposition,[status(thm)],[c_2247,c_10])).

cnf(c_9,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2983,plain,
    ( sK2(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    inference(superposition,[status(thm)],[c_2250,c_9])).

cnf(c_3099,plain,
    ( k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(k1_mcart_1(sK8))) = k1_mcart_1(sK8) ),
    inference(demodulation,[status(thm)],[c_2983,c_2250])).

cnf(c_2251,plain,
    ( sK3(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8) ),
    inference(superposition,[status(thm)],[c_2247,c_9])).

cnf(c_2424,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(sK8)) = sK8 ),
    inference(demodulation,[status(thm)],[c_2251,c_2247])).

cnf(c_4281,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(k1_mcart_1(sK8))),k2_mcart_1(sK8)) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_2424,c_2983])).

cnf(c_4465,plain,
    ( k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8)) = sK8 ),
    inference(demodulation,[status(thm)],[c_3099,c_4281])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
    | k11_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X3
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_312,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X7
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2260,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8))) = sK3(sK4,sK5,sK6,sK7,sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2247,c_312])).

cnf(c_2699,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(sK8))) = k2_mcart_1(sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2260,c_2251])).

cnf(c_2819,plain,
    ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2250,c_2699])).

cnf(c_4594,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(sK8)
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_308,c_2819])).

cnf(c_4595,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4594,c_16,c_15,c_14,c_13,c_154,c_474,c_476,c_478,c_480])).

cnf(c_4975,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8) ),
    inference(demodulation,[status(thm)],[c_4465,c_4595])).

cnf(c_6,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
    | k10_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X2
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_311,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X6
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2261,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8))) = sK2(sK4,sK5,sK6,sK7,sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2247,c_311])).

cnf(c_2686,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(sK8))) = sK2(sK4,sK5,sK6,sK7,sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2261,c_2251])).

cnf(c_2820,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = sK2(sK4,sK5,sK6,sK7,sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2250,c_2686])).

cnf(c_4694,plain,
    ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2820,c_2983])).

cnf(c_4702,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(sK8))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_308,c_4694])).

cnf(c_4703,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4702,c_16,c_15,c_14,c_13,c_154,c_474,c_476,c_478,c_480])).

cnf(c_4970,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    inference(demodulation,[status(thm)],[c_4465,c_4703])).

cnf(c_7,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
    | k9_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X1
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_310,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X5
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2262,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8))) = sK1(sK4,sK5,sK6,sK7,sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2247,c_310])).

cnf(c_2673,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(sK8))) = sK1(sK4,sK5,sK6,sK7,sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2262,c_2251])).

cnf(c_2821,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = sK1(sK4,sK5,sK6,sK7,sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2250,c_2673])).

cnf(c_2982,plain,
    ( k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)) = k1_mcart_1(k1_mcart_1(sK8)) ),
    inference(superposition,[status(thm)],[c_2250,c_10])).

cnf(c_3550,plain,
    ( sK1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(superposition,[status(thm)],[c_2982,c_9])).

cnf(c_4707,plain,
    ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2821,c_3550])).

cnf(c_4715,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_308,c_4707])).

cnf(c_4744,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4715,c_16,c_15,c_14,c_13,c_154,c_474,c_476,c_478,c_480])).

cnf(c_4968,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(demodulation,[status(thm)],[c_4465,c_4744])).

cnf(c_8,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
    | k8_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X0
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_309,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X4
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2263,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8))) = sK0(sK4,sK5,sK6,sK7,sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2247,c_309])).

cnf(c_2660,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(sK8))) = sK0(sK4,sK5,sK6,sK7,sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2263,c_2251])).

cnf(c_2822,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = sK0(sK4,sK5,sK6,sK7,sK8)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2250,c_2660])).

cnf(c_3549,plain,
    ( sK0(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(superposition,[status(thm)],[c_2982,c_10])).

cnf(c_4748,plain,
    ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2822,c_3549])).

cnf(c_4756,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_308,c_4748])).

cnf(c_4757,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4756,c_16,c_15,c_14,c_13,c_154,c_474,c_476,c_478,c_480])).

cnf(c_4966,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    inference(demodulation,[status(thm)],[c_4465,c_4757])).

cnf(c_11,negated_conjecture,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8))
    | k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(sK8) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4975,c_4970,c_4968,c_4966,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:18:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.64/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.01  
% 2.64/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.64/1.01  
% 2.64/1.01  ------  iProver source info
% 2.64/1.01  
% 2.64/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.64/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.64/1.01  git: non_committed_changes: false
% 2.64/1.01  git: last_make_outside_of_git: false
% 2.64/1.01  
% 2.64/1.01  ------ 
% 2.64/1.01  
% 2.64/1.01  ------ Input Options
% 2.64/1.01  
% 2.64/1.01  --out_options                           all
% 2.64/1.01  --tptp_safe_out                         true
% 2.64/1.01  --problem_path                          ""
% 2.64/1.01  --include_path                          ""
% 2.64/1.01  --clausifier                            res/vclausify_rel
% 2.64/1.01  --clausifier_options                    --mode clausify
% 2.64/1.01  --stdin                                 false
% 2.64/1.01  --stats_out                             all
% 2.64/1.01  
% 2.64/1.01  ------ General Options
% 2.64/1.01  
% 2.64/1.01  --fof                                   false
% 2.64/1.01  --time_out_real                         305.
% 2.64/1.01  --time_out_virtual                      -1.
% 2.64/1.01  --symbol_type_check                     false
% 2.64/1.01  --clausify_out                          false
% 2.64/1.01  --sig_cnt_out                           false
% 2.64/1.01  --trig_cnt_out                          false
% 2.64/1.01  --trig_cnt_out_tolerance                1.
% 2.64/1.01  --trig_cnt_out_sk_spl                   false
% 2.64/1.01  --abstr_cl_out                          false
% 2.64/1.01  
% 2.64/1.01  ------ Global Options
% 2.64/1.01  
% 2.64/1.01  --schedule                              default
% 2.64/1.01  --add_important_lit                     false
% 2.64/1.01  --prop_solver_per_cl                    1000
% 2.64/1.01  --min_unsat_core                        false
% 2.64/1.01  --soft_assumptions                      false
% 2.64/1.01  --soft_lemma_size                       3
% 2.64/1.01  --prop_impl_unit_size                   0
% 2.64/1.01  --prop_impl_unit                        []
% 2.64/1.01  --share_sel_clauses                     true
% 2.64/1.01  --reset_solvers                         false
% 2.64/1.01  --bc_imp_inh                            [conj_cone]
% 2.64/1.01  --conj_cone_tolerance                   3.
% 2.64/1.01  --extra_neg_conj                        none
% 2.64/1.01  --large_theory_mode                     true
% 2.64/1.01  --prolific_symb_bound                   200
% 2.64/1.01  --lt_threshold                          2000
% 2.64/1.01  --clause_weak_htbl                      true
% 2.64/1.01  --gc_record_bc_elim                     false
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing Options
% 2.64/1.01  
% 2.64/1.01  --preprocessing_flag                    true
% 2.64/1.01  --time_out_prep_mult                    0.1
% 2.64/1.01  --splitting_mode                        input
% 2.64/1.01  --splitting_grd                         true
% 2.64/1.01  --splitting_cvd                         false
% 2.64/1.01  --splitting_cvd_svl                     false
% 2.64/1.01  --splitting_nvd                         32
% 2.64/1.01  --sub_typing                            true
% 2.64/1.01  --prep_gs_sim                           true
% 2.64/1.01  --prep_unflatten                        true
% 2.64/1.01  --prep_res_sim                          true
% 2.64/1.01  --prep_upred                            true
% 2.64/1.01  --prep_sem_filter                       exhaustive
% 2.64/1.01  --prep_sem_filter_out                   false
% 2.64/1.01  --pred_elim                             true
% 2.64/1.01  --res_sim_input                         true
% 2.64/1.01  --eq_ax_congr_red                       true
% 2.64/1.01  --pure_diseq_elim                       true
% 2.64/1.01  --brand_transform                       false
% 2.64/1.01  --non_eq_to_eq                          false
% 2.64/1.01  --prep_def_merge                        true
% 2.64/1.01  --prep_def_merge_prop_impl              false
% 2.64/1.01  --prep_def_merge_mbd                    true
% 2.64/1.01  --prep_def_merge_tr_red                 false
% 2.64/1.01  --prep_def_merge_tr_cl                  false
% 2.64/1.01  --smt_preprocessing                     true
% 2.64/1.01  --smt_ac_axioms                         fast
% 2.64/1.01  --preprocessed_out                      false
% 2.64/1.01  --preprocessed_stats                    false
% 2.64/1.01  
% 2.64/1.01  ------ Abstraction refinement Options
% 2.64/1.01  
% 2.64/1.01  --abstr_ref                             []
% 2.64/1.01  --abstr_ref_prep                        false
% 2.64/1.01  --abstr_ref_until_sat                   false
% 2.64/1.01  --abstr_ref_sig_restrict                funpre
% 2.64/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/1.01  --abstr_ref_under                       []
% 2.64/1.01  
% 2.64/1.01  ------ SAT Options
% 2.64/1.01  
% 2.64/1.01  --sat_mode                              false
% 2.64/1.01  --sat_fm_restart_options                ""
% 2.64/1.01  --sat_gr_def                            false
% 2.64/1.01  --sat_epr_types                         true
% 2.64/1.01  --sat_non_cyclic_types                  false
% 2.64/1.01  --sat_finite_models                     false
% 2.64/1.01  --sat_fm_lemmas                         false
% 2.64/1.01  --sat_fm_prep                           false
% 2.64/1.01  --sat_fm_uc_incr                        true
% 2.64/1.01  --sat_out_model                         small
% 2.64/1.01  --sat_out_clauses                       false
% 2.64/1.01  
% 2.64/1.01  ------ QBF Options
% 2.64/1.01  
% 2.64/1.01  --qbf_mode                              false
% 2.64/1.01  --qbf_elim_univ                         false
% 2.64/1.01  --qbf_dom_inst                          none
% 2.64/1.01  --qbf_dom_pre_inst                      false
% 2.64/1.01  --qbf_sk_in                             false
% 2.64/1.01  --qbf_pred_elim                         true
% 2.64/1.01  --qbf_split                             512
% 2.64/1.01  
% 2.64/1.01  ------ BMC1 Options
% 2.64/1.01  
% 2.64/1.01  --bmc1_incremental                      false
% 2.64/1.01  --bmc1_axioms                           reachable_all
% 2.64/1.01  --bmc1_min_bound                        0
% 2.64/1.01  --bmc1_max_bound                        -1
% 2.64/1.01  --bmc1_max_bound_default                -1
% 2.64/1.01  --bmc1_symbol_reachability              true
% 2.64/1.01  --bmc1_property_lemmas                  false
% 2.64/1.01  --bmc1_k_induction                      false
% 2.64/1.01  --bmc1_non_equiv_states                 false
% 2.64/1.01  --bmc1_deadlock                         false
% 2.64/1.01  --bmc1_ucm                              false
% 2.64/1.01  --bmc1_add_unsat_core                   none
% 2.64/1.01  --bmc1_unsat_core_children              false
% 2.64/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/1.01  --bmc1_out_stat                         full
% 2.64/1.01  --bmc1_ground_init                      false
% 2.64/1.01  --bmc1_pre_inst_next_state              false
% 2.64/1.01  --bmc1_pre_inst_state                   false
% 2.64/1.01  --bmc1_pre_inst_reach_state             false
% 2.64/1.01  --bmc1_out_unsat_core                   false
% 2.64/1.01  --bmc1_aig_witness_out                  false
% 2.64/1.01  --bmc1_verbose                          false
% 2.64/1.01  --bmc1_dump_clauses_tptp                false
% 2.64/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.64/1.01  --bmc1_dump_file                        -
% 2.64/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.64/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.64/1.01  --bmc1_ucm_extend_mode                  1
% 2.64/1.01  --bmc1_ucm_init_mode                    2
% 2.64/1.01  --bmc1_ucm_cone_mode                    none
% 2.64/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.64/1.01  --bmc1_ucm_relax_model                  4
% 2.64/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.64/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/1.01  --bmc1_ucm_layered_model                none
% 2.64/1.01  --bmc1_ucm_max_lemma_size               10
% 2.64/1.01  
% 2.64/1.01  ------ AIG Options
% 2.64/1.01  
% 2.64/1.01  --aig_mode                              false
% 2.64/1.01  
% 2.64/1.01  ------ Instantiation Options
% 2.64/1.01  
% 2.64/1.01  --instantiation_flag                    true
% 2.64/1.01  --inst_sos_flag                         false
% 2.64/1.01  --inst_sos_phase                        true
% 2.64/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel_side                     num_symb
% 2.64/1.01  --inst_solver_per_active                1400
% 2.64/1.01  --inst_solver_calls_frac                1.
% 2.64/1.01  --inst_passive_queue_type               priority_queues
% 2.64/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/1.01  --inst_passive_queues_freq              [25;2]
% 2.64/1.01  --inst_dismatching                      true
% 2.64/1.01  --inst_eager_unprocessed_to_passive     true
% 2.64/1.01  --inst_prop_sim_given                   true
% 2.64/1.01  --inst_prop_sim_new                     false
% 2.64/1.01  --inst_subs_new                         false
% 2.64/1.01  --inst_eq_res_simp                      false
% 2.64/1.01  --inst_subs_given                       false
% 2.64/1.01  --inst_orphan_elimination               true
% 2.64/1.01  --inst_learning_loop_flag               true
% 2.64/1.01  --inst_learning_start                   3000
% 2.64/1.01  --inst_learning_factor                  2
% 2.64/1.01  --inst_start_prop_sim_after_learn       3
% 2.64/1.01  --inst_sel_renew                        solver
% 2.64/1.01  --inst_lit_activity_flag                true
% 2.64/1.01  --inst_restr_to_given                   false
% 2.64/1.01  --inst_activity_threshold               500
% 2.64/1.01  --inst_out_proof                        true
% 2.64/1.01  
% 2.64/1.01  ------ Resolution Options
% 2.64/1.01  
% 2.64/1.01  --resolution_flag                       true
% 2.64/1.01  --res_lit_sel                           adaptive
% 2.64/1.01  --res_lit_sel_side                      none
% 2.64/1.01  --res_ordering                          kbo
% 2.64/1.01  --res_to_prop_solver                    active
% 2.64/1.01  --res_prop_simpl_new                    false
% 2.64/1.01  --res_prop_simpl_given                  true
% 2.64/1.01  --res_passive_queue_type                priority_queues
% 2.64/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/1.01  --res_passive_queues_freq               [15;5]
% 2.64/1.01  --res_forward_subs                      full
% 2.64/1.01  --res_backward_subs                     full
% 2.64/1.01  --res_forward_subs_resolution           true
% 2.64/1.01  --res_backward_subs_resolution          true
% 2.64/1.01  --res_orphan_elimination                true
% 2.64/1.01  --res_time_limit                        2.
% 2.64/1.01  --res_out_proof                         true
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Options
% 2.64/1.01  
% 2.64/1.01  --superposition_flag                    true
% 2.64/1.01  --sup_passive_queue_type                priority_queues
% 2.64/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.64/1.01  --demod_completeness_check              fast
% 2.64/1.01  --demod_use_ground                      true
% 2.64/1.01  --sup_to_prop_solver                    passive
% 2.64/1.01  --sup_prop_simpl_new                    true
% 2.64/1.01  --sup_prop_simpl_given                  true
% 2.64/1.01  --sup_fun_splitting                     false
% 2.64/1.01  --sup_smt_interval                      50000
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Simplification Setup
% 2.64/1.01  
% 2.64/1.01  --sup_indices_passive                   []
% 2.64/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_full_bw                           [BwDemod]
% 2.64/1.01  --sup_immed_triv                        [TrivRules]
% 2.64/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_immed_bw_main                     []
% 2.64/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  
% 2.64/1.01  ------ Combination Options
% 2.64/1.01  
% 2.64/1.01  --comb_res_mult                         3
% 2.64/1.01  --comb_sup_mult                         2
% 2.64/1.01  --comb_inst_mult                        10
% 2.64/1.01  
% 2.64/1.01  ------ Debug Options
% 2.64/1.01  
% 2.64/1.01  --dbg_backtrace                         false
% 2.64/1.01  --dbg_dump_prop_clauses                 false
% 2.64/1.01  --dbg_dump_prop_clauses_file            -
% 2.64/1.01  --dbg_out_stat                          false
% 2.64/1.01  ------ Parsing...
% 2.64/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.64/1.01  ------ Proving...
% 2.64/1.01  ------ Problem Properties 
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  clauses                                 17
% 2.64/1.01  conjectures                             6
% 2.64/1.01  EPR                                     4
% 2.64/1.01  Horn                                    8
% 2.64/1.01  unary                                   7
% 2.64/1.01  binary                                  0
% 2.64/1.01  lits                                    65
% 2.64/1.01  lits eq                                 51
% 2.64/1.01  fd_pure                                 0
% 2.64/1.01  fd_pseudo                               0
% 2.64/1.01  fd_cond                                 4
% 2.64/1.01  fd_pseudo_cond                          0
% 2.64/1.01  AC symbols                              0
% 2.64/1.01  
% 2.64/1.01  ------ Schedule dynamic 5 is on 
% 2.64/1.01  
% 2.64/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  ------ 
% 2.64/1.01  Current options:
% 2.64/1.01  ------ 
% 2.64/1.01  
% 2.64/1.01  ------ Input Options
% 2.64/1.01  
% 2.64/1.01  --out_options                           all
% 2.64/1.01  --tptp_safe_out                         true
% 2.64/1.01  --problem_path                          ""
% 2.64/1.01  --include_path                          ""
% 2.64/1.01  --clausifier                            res/vclausify_rel
% 2.64/1.01  --clausifier_options                    --mode clausify
% 2.64/1.01  --stdin                                 false
% 2.64/1.01  --stats_out                             all
% 2.64/1.01  
% 2.64/1.01  ------ General Options
% 2.64/1.01  
% 2.64/1.01  --fof                                   false
% 2.64/1.01  --time_out_real                         305.
% 2.64/1.01  --time_out_virtual                      -1.
% 2.64/1.01  --symbol_type_check                     false
% 2.64/1.01  --clausify_out                          false
% 2.64/1.01  --sig_cnt_out                           false
% 2.64/1.01  --trig_cnt_out                          false
% 2.64/1.01  --trig_cnt_out_tolerance                1.
% 2.64/1.01  --trig_cnt_out_sk_spl                   false
% 2.64/1.01  --abstr_cl_out                          false
% 2.64/1.01  
% 2.64/1.01  ------ Global Options
% 2.64/1.01  
% 2.64/1.01  --schedule                              default
% 2.64/1.01  --add_important_lit                     false
% 2.64/1.01  --prop_solver_per_cl                    1000
% 2.64/1.01  --min_unsat_core                        false
% 2.64/1.01  --soft_assumptions                      false
% 2.64/1.01  --soft_lemma_size                       3
% 2.64/1.01  --prop_impl_unit_size                   0
% 2.64/1.01  --prop_impl_unit                        []
% 2.64/1.01  --share_sel_clauses                     true
% 2.64/1.01  --reset_solvers                         false
% 2.64/1.01  --bc_imp_inh                            [conj_cone]
% 2.64/1.01  --conj_cone_tolerance                   3.
% 2.64/1.01  --extra_neg_conj                        none
% 2.64/1.01  --large_theory_mode                     true
% 2.64/1.01  --prolific_symb_bound                   200
% 2.64/1.01  --lt_threshold                          2000
% 2.64/1.01  --clause_weak_htbl                      true
% 2.64/1.01  --gc_record_bc_elim                     false
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing Options
% 2.64/1.01  
% 2.64/1.01  --preprocessing_flag                    true
% 2.64/1.01  --time_out_prep_mult                    0.1
% 2.64/1.01  --splitting_mode                        input
% 2.64/1.01  --splitting_grd                         true
% 2.64/1.01  --splitting_cvd                         false
% 2.64/1.01  --splitting_cvd_svl                     false
% 2.64/1.01  --splitting_nvd                         32
% 2.64/1.01  --sub_typing                            true
% 2.64/1.01  --prep_gs_sim                           true
% 2.64/1.01  --prep_unflatten                        true
% 2.64/1.01  --prep_res_sim                          true
% 2.64/1.01  --prep_upred                            true
% 2.64/1.01  --prep_sem_filter                       exhaustive
% 2.64/1.01  --prep_sem_filter_out                   false
% 2.64/1.01  --pred_elim                             true
% 2.64/1.01  --res_sim_input                         true
% 2.64/1.01  --eq_ax_congr_red                       true
% 2.64/1.01  --pure_diseq_elim                       true
% 2.64/1.01  --brand_transform                       false
% 2.64/1.01  --non_eq_to_eq                          false
% 2.64/1.01  --prep_def_merge                        true
% 2.64/1.01  --prep_def_merge_prop_impl              false
% 2.64/1.01  --prep_def_merge_mbd                    true
% 2.64/1.01  --prep_def_merge_tr_red                 false
% 2.64/1.01  --prep_def_merge_tr_cl                  false
% 2.64/1.01  --smt_preprocessing                     true
% 2.64/1.01  --smt_ac_axioms                         fast
% 2.64/1.01  --preprocessed_out                      false
% 2.64/1.01  --preprocessed_stats                    false
% 2.64/1.01  
% 2.64/1.01  ------ Abstraction refinement Options
% 2.64/1.01  
% 2.64/1.01  --abstr_ref                             []
% 2.64/1.01  --abstr_ref_prep                        false
% 2.64/1.01  --abstr_ref_until_sat                   false
% 2.64/1.01  --abstr_ref_sig_restrict                funpre
% 2.64/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/1.01  --abstr_ref_under                       []
% 2.64/1.01  
% 2.64/1.01  ------ SAT Options
% 2.64/1.01  
% 2.64/1.01  --sat_mode                              false
% 2.64/1.01  --sat_fm_restart_options                ""
% 2.64/1.01  --sat_gr_def                            false
% 2.64/1.01  --sat_epr_types                         true
% 2.64/1.01  --sat_non_cyclic_types                  false
% 2.64/1.01  --sat_finite_models                     false
% 2.64/1.01  --sat_fm_lemmas                         false
% 2.64/1.01  --sat_fm_prep                           false
% 2.64/1.01  --sat_fm_uc_incr                        true
% 2.64/1.01  --sat_out_model                         small
% 2.64/1.01  --sat_out_clauses                       false
% 2.64/1.01  
% 2.64/1.01  ------ QBF Options
% 2.64/1.01  
% 2.64/1.01  --qbf_mode                              false
% 2.64/1.01  --qbf_elim_univ                         false
% 2.64/1.01  --qbf_dom_inst                          none
% 2.64/1.01  --qbf_dom_pre_inst                      false
% 2.64/1.01  --qbf_sk_in                             false
% 2.64/1.01  --qbf_pred_elim                         true
% 2.64/1.01  --qbf_split                             512
% 2.64/1.01  
% 2.64/1.01  ------ BMC1 Options
% 2.64/1.01  
% 2.64/1.01  --bmc1_incremental                      false
% 2.64/1.01  --bmc1_axioms                           reachable_all
% 2.64/1.01  --bmc1_min_bound                        0
% 2.64/1.01  --bmc1_max_bound                        -1
% 2.64/1.01  --bmc1_max_bound_default                -1
% 2.64/1.01  --bmc1_symbol_reachability              true
% 2.64/1.01  --bmc1_property_lemmas                  false
% 2.64/1.01  --bmc1_k_induction                      false
% 2.64/1.01  --bmc1_non_equiv_states                 false
% 2.64/1.01  --bmc1_deadlock                         false
% 2.64/1.01  --bmc1_ucm                              false
% 2.64/1.01  --bmc1_add_unsat_core                   none
% 2.64/1.01  --bmc1_unsat_core_children              false
% 2.64/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/1.01  --bmc1_out_stat                         full
% 2.64/1.01  --bmc1_ground_init                      false
% 2.64/1.01  --bmc1_pre_inst_next_state              false
% 2.64/1.01  --bmc1_pre_inst_state                   false
% 2.64/1.01  --bmc1_pre_inst_reach_state             false
% 2.64/1.01  --bmc1_out_unsat_core                   false
% 2.64/1.01  --bmc1_aig_witness_out                  false
% 2.64/1.01  --bmc1_verbose                          false
% 2.64/1.01  --bmc1_dump_clauses_tptp                false
% 2.64/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.64/1.01  --bmc1_dump_file                        -
% 2.64/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.64/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.64/1.01  --bmc1_ucm_extend_mode                  1
% 2.64/1.01  --bmc1_ucm_init_mode                    2
% 2.64/1.01  --bmc1_ucm_cone_mode                    none
% 2.64/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.64/1.01  --bmc1_ucm_relax_model                  4
% 2.64/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.64/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/1.01  --bmc1_ucm_layered_model                none
% 2.64/1.01  --bmc1_ucm_max_lemma_size               10
% 2.64/1.01  
% 2.64/1.01  ------ AIG Options
% 2.64/1.01  
% 2.64/1.01  --aig_mode                              false
% 2.64/1.01  
% 2.64/1.01  ------ Instantiation Options
% 2.64/1.01  
% 2.64/1.01  --instantiation_flag                    true
% 2.64/1.01  --inst_sos_flag                         false
% 2.64/1.01  --inst_sos_phase                        true
% 2.64/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel_side                     none
% 2.64/1.01  --inst_solver_per_active                1400
% 2.64/1.01  --inst_solver_calls_frac                1.
% 2.64/1.01  --inst_passive_queue_type               priority_queues
% 2.64/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/1.01  --inst_passive_queues_freq              [25;2]
% 2.64/1.01  --inst_dismatching                      true
% 2.64/1.01  --inst_eager_unprocessed_to_passive     true
% 2.64/1.01  --inst_prop_sim_given                   true
% 2.64/1.01  --inst_prop_sim_new                     false
% 2.64/1.01  --inst_subs_new                         false
% 2.64/1.01  --inst_eq_res_simp                      false
% 2.64/1.01  --inst_subs_given                       false
% 2.64/1.01  --inst_orphan_elimination               true
% 2.64/1.01  --inst_learning_loop_flag               true
% 2.64/1.01  --inst_learning_start                   3000
% 2.64/1.01  --inst_learning_factor                  2
% 2.64/1.01  --inst_start_prop_sim_after_learn       3
% 2.64/1.01  --inst_sel_renew                        solver
% 2.64/1.01  --inst_lit_activity_flag                true
% 2.64/1.01  --inst_restr_to_given                   false
% 2.64/1.01  --inst_activity_threshold               500
% 2.64/1.01  --inst_out_proof                        true
% 2.64/1.01  
% 2.64/1.01  ------ Resolution Options
% 2.64/1.01  
% 2.64/1.01  --resolution_flag                       false
% 2.64/1.01  --res_lit_sel                           adaptive
% 2.64/1.01  --res_lit_sel_side                      none
% 2.64/1.01  --res_ordering                          kbo
% 2.64/1.01  --res_to_prop_solver                    active
% 2.64/1.01  --res_prop_simpl_new                    false
% 2.64/1.01  --res_prop_simpl_given                  true
% 2.64/1.01  --res_passive_queue_type                priority_queues
% 2.64/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/1.01  --res_passive_queues_freq               [15;5]
% 2.64/1.01  --res_forward_subs                      full
% 2.64/1.01  --res_backward_subs                     full
% 2.64/1.01  --res_forward_subs_resolution           true
% 2.64/1.01  --res_backward_subs_resolution          true
% 2.64/1.01  --res_orphan_elimination                true
% 2.64/1.01  --res_time_limit                        2.
% 2.64/1.01  --res_out_proof                         true
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Options
% 2.64/1.01  
% 2.64/1.01  --superposition_flag                    true
% 2.64/1.01  --sup_passive_queue_type                priority_queues
% 2.64/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.64/1.01  --demod_completeness_check              fast
% 2.64/1.01  --demod_use_ground                      true
% 2.64/1.01  --sup_to_prop_solver                    passive
% 2.64/1.01  --sup_prop_simpl_new                    true
% 2.64/1.01  --sup_prop_simpl_given                  true
% 2.64/1.01  --sup_fun_splitting                     false
% 2.64/1.01  --sup_smt_interval                      50000
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Simplification Setup
% 2.64/1.01  
% 2.64/1.01  --sup_indices_passive                   []
% 2.64/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_full_bw                           [BwDemod]
% 2.64/1.01  --sup_immed_triv                        [TrivRules]
% 2.64/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_immed_bw_main                     []
% 2.64/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  
% 2.64/1.01  ------ Combination Options
% 2.64/1.01  
% 2.64/1.01  --comb_res_mult                         3
% 2.64/1.01  --comb_sup_mult                         2
% 2.64/1.01  --comb_inst_mult                        10
% 2.64/1.01  
% 2.64/1.01  ------ Debug Options
% 2.64/1.01  
% 2.64/1.01  --dbg_backtrace                         false
% 2.64/1.01  --dbg_dump_prop_clauses                 false
% 2.64/1.01  --dbg_dump_prop_clauses_file            -
% 2.64/1.01  --dbg_out_stat                          false
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  ------ Proving...
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  % SZS status Theorem for theBenchmark.p
% 2.64/1.01  
% 2.64/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.64/1.01  
% 2.64/1.01  fof(f7,conjecture,(
% 2.64/1.01    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f8,negated_conjecture,(
% 2.64/1.01    ~! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.64/1.01    inference(negated_conjecture,[],[f7])).
% 2.64/1.01  
% 2.64/1.01  fof(f11,plain,(
% 2.64/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4) | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4)) | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.64/1.01    inference(ennf_transformation,[],[f8])).
% 2.64/1.01  
% 2.64/1.01  fof(f18,plain,(
% 2.64/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4) | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4)) | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) => ((k11_mcart_1(X0,X1,X2,X3,sK8) != k2_mcart_1(sK8) | k10_mcart_1(X0,X1,X2,X3,sK8) != k2_mcart_1(k1_mcart_1(sK8)) | k9_mcart_1(X0,X1,X2,X3,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k8_mcart_1(X0,X1,X2,X3,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))) & m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3)))) )),
% 2.64/1.01    introduced(choice_axiom,[])).
% 2.64/1.01  
% 2.64/1.01  fof(f17,plain,(
% 2.64/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(X4) | k10_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(X4)) | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X4] : ((k11_mcart_1(sK4,sK5,sK6,sK7,X4) != k2_mcart_1(X4) | k10_mcart_1(sK4,sK5,sK6,sK7,X4) != k2_mcart_1(k1_mcart_1(X4)) | k9_mcart_1(sK4,sK5,sK6,sK7,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k8_mcart_1(sK4,sK5,sK6,sK7,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) & m1_subset_1(X4,k4_zfmisc_1(sK4,sK5,sK6,sK7))) & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4)),
% 2.64/1.01    introduced(choice_axiom,[])).
% 2.64/1.01  
% 2.64/1.01  fof(f19,plain,(
% 2.64/1.01    ((k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(sK8) | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8)) | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))) & m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))) & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4),
% 2.64/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f11,f18,f17])).
% 2.64/1.01  
% 2.64/1.01  fof(f38,plain,(
% 2.64/1.01    m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.64/1.01    inference(cnf_transformation,[],[f19])).
% 2.64/1.01  
% 2.64/1.01  fof(f3,axiom,(
% 2.64/1.01    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f22,plain,(
% 2.64/1.01    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f3])).
% 2.64/1.01  
% 2.64/1.01  fof(f50,plain,(
% 2.64/1.01    m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7))),
% 2.64/1.01    inference(definition_unfolding,[],[f38,f22])).
% 2.64/1.01  
% 2.64/1.01  fof(f4,axiom,(
% 2.64/1.01    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f9,plain,(
% 2.64/1.01    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.64/1.01    inference(ennf_transformation,[],[f4])).
% 2.64/1.01  
% 2.64/1.01  fof(f15,plain,(
% 2.64/1.01    ( ! [X6,X7,X5] : (! [X4,X3,X2,X1,X0] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) => (k4_mcart_1(X5,X6,X7,sK3(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)))) )),
% 2.64/1.01    introduced(choice_axiom,[])).
% 2.64/1.01  
% 2.64/1.01  fof(f14,plain,(
% 2.64/1.01    ( ! [X6,X5] : (! [X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) => (? [X8] : (k4_mcart_1(X5,X6,sK2(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)))) )),
% 2.64/1.01    introduced(choice_axiom,[])).
% 2.64/1.01  
% 2.64/1.01  fof(f13,plain,(
% 2.64/1.01    ( ! [X5] : (! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (? [X8] : (k4_mcart_1(X5,sK1(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)))) )),
% 2.64/1.01    introduced(choice_axiom,[])).
% 2.64/1.01  
% 2.64/1.01  fof(f12,plain,(
% 2.64/1.01    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK0(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)))),
% 2.64/1.01    introduced(choice_axiom,[])).
% 2.64/1.01  
% 2.64/1.01  fof(f16,plain,(
% 2.64/1.01    ! [X0,X1,X2,X3] : (! [X4] : (((((k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK3(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK2(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.64/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f15,f14,f13,f12])).
% 2.64/1.01  
% 2.64/1.01  fof(f27,plain,(
% 2.64/1.01    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(cnf_transformation,[],[f16])).
% 2.64/1.01  
% 2.64/1.01  fof(f2,axiom,(
% 2.64/1.01    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f21,plain,(
% 2.64/1.01    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f2])).
% 2.64/1.01  
% 2.64/1.01  fof(f1,axiom,(
% 2.64/1.01    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f20,plain,(
% 2.64/1.01    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f1])).
% 2.64/1.01  
% 2.64/1.01  fof(f40,plain,(
% 2.64/1.01    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 2.64/1.01    inference(definition_unfolding,[],[f21,f20])).
% 2.64/1.01  
% 2.64/1.01  fof(f41,plain,(
% 2.64/1.01    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(definition_unfolding,[],[f27,f40,f22])).
% 2.64/1.01  
% 2.64/1.01  fof(f34,plain,(
% 2.64/1.01    k1_xboole_0 != sK4),
% 2.64/1.01    inference(cnf_transformation,[],[f19])).
% 2.64/1.01  
% 2.64/1.01  fof(f35,plain,(
% 2.64/1.01    k1_xboole_0 != sK5),
% 2.64/1.01    inference(cnf_transformation,[],[f19])).
% 2.64/1.01  
% 2.64/1.01  fof(f36,plain,(
% 2.64/1.01    k1_xboole_0 != sK6),
% 2.64/1.01    inference(cnf_transformation,[],[f19])).
% 2.64/1.01  
% 2.64/1.01  fof(f37,plain,(
% 2.64/1.01    k1_xboole_0 != sK7),
% 2.64/1.01    inference(cnf_transformation,[],[f19])).
% 2.64/1.01  
% 2.64/1.01  fof(f6,axiom,(
% 2.64/1.01    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f32,plain,(
% 2.64/1.01    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.64/1.01    inference(cnf_transformation,[],[f6])).
% 2.64/1.01  
% 2.64/1.01  fof(f33,plain,(
% 2.64/1.01    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.64/1.01    inference(cnf_transformation,[],[f6])).
% 2.64/1.01  
% 2.64/1.01  fof(f5,axiom,(
% 2.64/1.01    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.64/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f10,plain,(
% 2.64/1.01    ! [X0,X1,X2,X3] : (! [X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.64/1.01    inference(ennf_transformation,[],[f5])).
% 2.64/1.01  
% 2.64/1.01  fof(f31,plain,(
% 2.64/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = X8 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(cnf_transformation,[],[f10])).
% 2.64/1.01  
% 2.64/1.01  fof(f46,plain,(
% 2.64/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = X8 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(definition_unfolding,[],[f31,f40,f22])).
% 2.64/1.01  
% 2.64/1.01  fof(f51,plain,(
% 2.64/1.01    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8 | ~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(equality_resolution,[],[f46])).
% 2.64/1.01  
% 2.64/1.01  fof(f30,plain,(
% 2.64/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = X7 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(cnf_transformation,[],[f10])).
% 2.64/1.01  
% 2.64/1.01  fof(f47,plain,(
% 2.64/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = X7 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(definition_unfolding,[],[f30,f40,f22])).
% 2.64/1.01  
% 2.64/1.01  fof(f52,plain,(
% 2.64/1.01    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X7 | ~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(equality_resolution,[],[f47])).
% 2.64/1.01  
% 2.64/1.01  fof(f29,plain,(
% 2.64/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = X6 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(cnf_transformation,[],[f10])).
% 2.64/1.01  
% 2.64/1.01  fof(f48,plain,(
% 2.64/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = X6 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(definition_unfolding,[],[f29,f40,f22])).
% 2.64/1.01  
% 2.64/1.01  fof(f53,plain,(
% 2.64/1.01    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6 | ~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(equality_resolution,[],[f48])).
% 2.64/1.01  
% 2.64/1.01  fof(f28,plain,(
% 2.64/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = X5 | k4_mcart_1(X5,X6,X7,X8) != X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(cnf_transformation,[],[f10])).
% 2.64/1.01  
% 2.64/1.01  fof(f49,plain,(
% 2.64/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = X5 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | ~m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(definition_unfolding,[],[f28,f40,f22])).
% 2.64/1.01  
% 2.64/1.01  fof(f54,plain,(
% 2.64/1.01    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5 | ~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.64/1.01    inference(equality_resolution,[],[f49])).
% 2.64/1.01  
% 2.64/1.01  fof(f39,plain,(
% 2.64/1.01    k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(sK8) | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8)) | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))),
% 2.64/1.01    inference(cnf_transformation,[],[f19])).
% 2.64/1.01  
% 2.64/1.01  cnf(c_12,negated_conjecture,
% 2.64/1.01      ( m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) ),
% 2.64/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_308,plain,
% 2.64/1.01      ( m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_0,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4))
% 2.64/1.01      | k4_tarski(k4_tarski(k4_tarski(sK0(X1,X2,X3,X4,X0),sK1(X1,X2,X3,X4,X0)),sK2(X1,X2,X3,X4,X0)),sK3(X1,X2,X3,X4,X0)) = X0
% 2.64/1.01      | k1_xboole_0 = X4
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1 ),
% 2.64/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_317,plain,
% 2.64/1.01      ( k4_tarski(k4_tarski(k4_tarski(sK0(X0,X1,X2,X3,X4),sK1(X0,X1,X2,X3,X4)),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)) = X4
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | m1_subset_1(X4,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2246,plain,
% 2.64/1.01      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8)) = sK8
% 2.64/1.01      | sK7 = k1_xboole_0
% 2.64/1.01      | sK6 = k1_xboole_0
% 2.64/1.01      | sK5 = k1_xboole_0
% 2.64/1.01      | sK4 = k1_xboole_0 ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_308,c_317]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_16,negated_conjecture,
% 2.64/1.01      ( k1_xboole_0 != sK4 ),
% 2.64/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_15,negated_conjecture,
% 2.64/1.01      ( k1_xboole_0 != sK5 ),
% 2.64/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_14,negated_conjecture,
% 2.64/1.01      ( k1_xboole_0 != sK6 ),
% 2.64/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_13,negated_conjecture,
% 2.64/1.01      ( k1_xboole_0 != sK7 ),
% 2.64/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_131,plain,( X0 = X0 ),theory(equality) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_154,plain,
% 2.64/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_131]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_132,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_473,plain,
% 2.64/1.01      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_132]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_474,plain,
% 2.64/1.01      ( sK7 != k1_xboole_0
% 2.64/1.01      | k1_xboole_0 = sK7
% 2.64/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_473]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_475,plain,
% 2.64/1.01      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_132]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_476,plain,
% 2.64/1.01      ( sK6 != k1_xboole_0
% 2.64/1.01      | k1_xboole_0 = sK6
% 2.64/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_475]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_477,plain,
% 2.64/1.01      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_132]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_478,plain,
% 2.64/1.01      ( sK5 != k1_xboole_0
% 2.64/1.01      | k1_xboole_0 = sK5
% 2.64/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_477]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_479,plain,
% 2.64/1.01      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_132]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_480,plain,
% 2.64/1.01      ( sK4 != k1_xboole_0
% 2.64/1.01      | k1_xboole_0 = sK4
% 2.64/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_479]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2247,plain,
% 2.64/1.01      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8)) = sK8 ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_2246,c_16,c_15,c_14,c_13,c_154,c_474,c_476,c_478,
% 2.64/1.01                 c_480]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_10,plain,
% 2.64/1.01      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 2.64/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2250,plain,
% 2.64/1.01      ( k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)) = k1_mcart_1(sK8) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2247,c_10]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_9,plain,
% 2.64/1.01      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 2.64/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2983,plain,
% 2.64/1.01      ( sK2(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2250,c_9]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3099,plain,
% 2.64/1.01      ( k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(k1_mcart_1(sK8))) = k1_mcart_1(sK8) ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2983,c_2250]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2251,plain,
% 2.64/1.01      ( sK3(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2247,c_9]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2424,plain,
% 2.64/1.01      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(sK8)) = sK8 ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2251,c_2247]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4281,plain,
% 2.64/1.01      ( k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(k1_mcart_1(sK8))),k2_mcart_1(sK8)) = sK8 ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_2424,c_2983]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4465,plain,
% 2.64/1.01      ( k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8)) = sK8 ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_3099,c_4281]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_5,plain,
% 2.64/1.01      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
% 2.64/1.01      | k11_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X3
% 2.64/1.01      | k1_xboole_0 = X7
% 2.64/1.01      | k1_xboole_0 = X6
% 2.64/1.01      | k1_xboole_0 = X5
% 2.64/1.01      | k1_xboole_0 = X4 ),
% 2.64/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_312,plain,
% 2.64/1.01      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X7
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2260,plain,
% 2.64/1.01      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8))) = sK3(sK4,sK5,sK6,sK7,sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2247,c_312]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2699,plain,
% 2.64/1.01      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(sK8))) = k2_mcart_1(sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_2260,c_2251]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2819,plain,
% 2.64/1.01      ( k11_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2250,c_2699]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4594,plain,
% 2.64/1.01      ( k11_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(sK8)
% 2.64/1.01      | sK7 = k1_xboole_0
% 2.64/1.01      | sK6 = k1_xboole_0
% 2.64/1.01      | sK5 = k1_xboole_0
% 2.64/1.01      | sK4 = k1_xboole_0 ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_308,c_2819]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4595,plain,
% 2.64/1.01      ( k11_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(sK8) ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_4594,c_16,c_15,c_14,c_13,c_154,c_474,c_476,c_478,
% 2.64/1.01                 c_480]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4975,plain,
% 2.64/1.01      ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8) ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_4465,c_4595]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_6,plain,
% 2.64/1.01      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
% 2.64/1.01      | k10_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X2
% 2.64/1.01      | k1_xboole_0 = X7
% 2.64/1.01      | k1_xboole_0 = X6
% 2.64/1.01      | k1_xboole_0 = X5
% 2.64/1.01      | k1_xboole_0 = X4 ),
% 2.64/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_311,plain,
% 2.64/1.01      ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X6
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2261,plain,
% 2.64/1.01      ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8))) = sK2(sK4,sK5,sK6,sK7,sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2247,c_311]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2686,plain,
% 2.64/1.01      ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(sK8))) = sK2(sK4,sK5,sK6,sK7,sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_2261,c_2251]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2820,plain,
% 2.64/1.01      ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = sK2(sK4,sK5,sK6,sK7,sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2250,c_2686]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4694,plain,
% 2.64/1.01      ( k10_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(sK8))
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_2820,c_2983]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4702,plain,
% 2.64/1.01      ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(sK8))
% 2.64/1.01      | sK7 = k1_xboole_0
% 2.64/1.01      | sK6 = k1_xboole_0
% 2.64/1.01      | sK5 = k1_xboole_0
% 2.64/1.01      | sK4 = k1_xboole_0 ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_308,c_4694]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4703,plain,
% 2.64/1.01      ( k10_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(sK8)) ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_4702,c_16,c_15,c_14,c_13,c_154,c_474,c_476,c_478,
% 2.64/1.01                 c_480]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4970,plain,
% 2.64/1.01      ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_4465,c_4703]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_7,plain,
% 2.64/1.01      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
% 2.64/1.01      | k9_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X1
% 2.64/1.01      | k1_xboole_0 = X7
% 2.64/1.01      | k1_xboole_0 = X6
% 2.64/1.01      | k1_xboole_0 = X5
% 2.64/1.01      | k1_xboole_0 = X4 ),
% 2.64/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_310,plain,
% 2.64/1.01      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X5
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2262,plain,
% 2.64/1.01      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8))) = sK1(sK4,sK5,sK6,sK7,sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2247,c_310]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2673,plain,
% 2.64/1.01      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(sK8))) = sK1(sK4,sK5,sK6,sK7,sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_2262,c_2251]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2821,plain,
% 2.64/1.01      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = sK1(sK4,sK5,sK6,sK7,sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2250,c_2673]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2982,plain,
% 2.64/1.01      ( k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)) = k1_mcart_1(k1_mcart_1(sK8)) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2250,c_10]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3550,plain,
% 2.64/1.01      ( sK1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2982,c_9]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4707,plain,
% 2.64/1.01      ( k9_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_2821,c_3550]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4715,plain,
% 2.64/1.01      ( k9_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 2.64/1.01      | sK7 = k1_xboole_0
% 2.64/1.01      | sK6 = k1_xboole_0
% 2.64/1.01      | sK5 = k1_xboole_0
% 2.64/1.01      | sK4 = k1_xboole_0 ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_308,c_4707]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4744,plain,
% 2.64/1.01      ( k9_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_4715,c_16,c_15,c_14,c_13,c_154,c_474,c_476,c_478,
% 2.64/1.01                 c_480]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4968,plain,
% 2.64/1.01      ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_4465,c_4744]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_8,plain,
% 2.64/1.01      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3),k2_zfmisc_1(k3_zfmisc_1(X4,X5,X6),X7))
% 2.64/1.01      | k8_mcart_1(X4,X5,X6,X7,k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) = X0
% 2.64/1.01      | k1_xboole_0 = X7
% 2.64/1.01      | k1_xboole_0 = X6
% 2.64/1.01      | k1_xboole_0 = X5
% 2.64/1.01      | k1_xboole_0 = X4 ),
% 2.64/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_309,plain,
% 2.64/1.01      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7)) = X4
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X4,X5),X6),X7),k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2263,plain,
% 2.64/1.01      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),sK3(sK4,sK5,sK6,sK7,sK8))) = sK0(sK4,sK5,sK6,sK7,sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2247,c_309]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2660,plain,
% 2.64/1.01      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(sK0(sK4,sK5,sK6,sK7,sK8),sK1(sK4,sK5,sK6,sK7,sK8)),sK2(sK4,sK5,sK6,sK7,sK8)),k2_mcart_1(sK8))) = sK0(sK4,sK5,sK6,sK7,sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_2263,c_2251]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2822,plain,
% 2.64/1.01      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = sK0(sK4,sK5,sK6,sK7,sK8)
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2250,c_2660]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3549,plain,
% 2.64/1.01      ( sK0(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2982,c_10]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4748,plain,
% 2.64/1.01      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 2.64/1.01      | k1_xboole_0 = X3
% 2.64/1.01      | k1_xboole_0 = X2
% 2.64/1.01      | k1_xboole_0 = X1
% 2.64/1.01      | k1_xboole_0 = X0
% 2.64/1.01      | m1_subset_1(sK8,k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_2822,c_3549]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4756,plain,
% 2.64/1.01      ( k8_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 2.64/1.01      | sK7 = k1_xboole_0
% 2.64/1.01      | sK6 = k1_xboole_0
% 2.64/1.01      | sK5 = k1_xboole_0
% 2.64/1.01      | sK4 = k1_xboole_0 ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_308,c_4748]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4757,plain,
% 2.64/1.01      ( k8_mcart_1(sK4,sK5,sK6,sK7,k4_tarski(k1_mcart_1(sK8),k2_mcart_1(sK8))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_4756,c_16,c_15,c_14,c_13,c_154,c_474,c_476,c_478,
% 2.64/1.01                 c_480]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4966,plain,
% 2.64/1.01      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_4465,c_4757]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_11,negated_conjecture,
% 2.64/1.01      ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 2.64/1.01      | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 2.64/1.01      | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8))
% 2.64/1.01      | k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(sK8) ),
% 2.64/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(contradiction,plain,
% 2.64/1.01      ( $false ),
% 2.64/1.01      inference(minisat,[status(thm)],[c_4975,c_4970,c_4968,c_4966,c_11]) ).
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.64/1.01  
% 2.64/1.01  ------                               Statistics
% 2.64/1.01  
% 2.64/1.01  ------ General
% 2.64/1.01  
% 2.64/1.01  abstr_ref_over_cycles:                  0
% 2.64/1.01  abstr_ref_under_cycles:                 0
% 2.64/1.01  gc_basic_clause_elim:                   0
% 2.64/1.01  forced_gc_time:                         0
% 2.64/1.01  parsing_time:                           0.009
% 2.64/1.01  unif_index_cands_time:                  0.
% 2.64/1.01  unif_index_add_time:                    0.
% 2.64/1.01  orderings_time:                         0.
% 2.64/1.01  out_proof_time:                         0.01
% 2.64/1.01  total_time:                             0.211
% 2.64/1.01  num_of_symbols:                         51
% 2.64/1.01  num_of_terms:                           11532
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing
% 2.64/1.01  
% 2.64/1.01  num_of_splits:                          0
% 2.64/1.01  num_of_split_atoms:                     0
% 2.64/1.01  num_of_reused_defs:                     0
% 2.64/1.01  num_eq_ax_congr_red:                    40
% 2.64/1.01  num_of_sem_filtered_clauses:            1
% 2.64/1.01  num_of_subtypes:                        0
% 2.64/1.01  monotx_restored_types:                  0
% 2.64/1.01  sat_num_of_epr_types:                   0
% 2.64/1.01  sat_num_of_non_cyclic_types:            0
% 2.64/1.01  sat_guarded_non_collapsed_types:        0
% 2.64/1.01  num_pure_diseq_elim:                    0
% 2.64/1.01  simp_replaced_by:                       0
% 2.64/1.01  res_preprocessed:                       76
% 2.64/1.01  prep_upred:                             0
% 2.64/1.01  prep_unflattend:                        0
% 2.64/1.01  smt_new_axioms:                         0
% 2.64/1.01  pred_elim_cands:                        1
% 2.64/1.01  pred_elim:                              0
% 2.64/1.01  pred_elim_cl:                           0
% 2.64/1.01  pred_elim_cycles:                       1
% 2.64/1.01  merged_defs:                            0
% 2.64/1.01  merged_defs_ncl:                        0
% 2.64/1.01  bin_hyper_res:                          0
% 2.64/1.01  prep_cycles:                            3
% 2.64/1.01  pred_elim_time:                         0.
% 2.64/1.01  splitting_time:                         0.
% 2.64/1.01  sem_filter_time:                        0.
% 2.64/1.01  monotx_time:                            0.001
% 2.64/1.01  subtype_inf_time:                       0.
% 2.64/1.01  
% 2.64/1.01  ------ Problem properties
% 2.64/1.01  
% 2.64/1.01  clauses:                                17
% 2.64/1.01  conjectures:                            6
% 2.64/1.01  epr:                                    4
% 2.64/1.01  horn:                                   8
% 2.64/1.01  ground:                                 6
% 2.64/1.01  unary:                                  7
% 2.64/1.01  binary:                                 0
% 2.64/1.01  lits:                                   65
% 2.64/1.01  lits_eq:                                51
% 2.64/1.01  fd_pure:                                0
% 2.64/1.01  fd_pseudo:                              0
% 2.64/1.01  fd_cond:                                4
% 2.64/1.01  fd_pseudo_cond:                         0
% 2.64/1.01  ac_symbols:                             0
% 2.64/1.01  
% 2.64/1.01  ------ Propositional Solver
% 2.64/1.01  
% 2.64/1.01  prop_solver_calls:                      22
% 2.64/1.01  prop_fast_solver_calls:                 821
% 2.64/1.01  smt_solver_calls:                       0
% 2.64/1.01  smt_fast_solver_calls:                  0
% 2.64/1.01  prop_num_of_clauses:                    1795
% 2.64/1.01  prop_preprocess_simplified:             6359
% 2.64/1.01  prop_fo_subsumed:                       36
% 2.64/1.01  prop_solver_time:                       0.
% 2.64/1.01  smt_solver_time:                        0.
% 2.64/1.01  smt_fast_solver_time:                   0.
% 2.64/1.01  prop_fast_solver_time:                  0.
% 2.64/1.01  prop_unsat_core_time:                   0.
% 2.64/1.01  
% 2.64/1.01  ------ QBF
% 2.64/1.01  
% 2.64/1.01  qbf_q_res:                              0
% 2.64/1.01  qbf_num_tautologies:                    0
% 2.64/1.01  qbf_prep_cycles:                        0
% 2.64/1.01  
% 2.64/1.01  ------ BMC1
% 2.64/1.01  
% 2.64/1.01  bmc1_current_bound:                     -1
% 2.64/1.01  bmc1_last_solved_bound:                 -1
% 2.64/1.01  bmc1_unsat_core_size:                   -1
% 2.64/1.01  bmc1_unsat_core_parents_size:           -1
% 2.64/1.01  bmc1_merge_next_fun:                    0
% 2.64/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.64/1.01  
% 2.64/1.01  ------ Instantiation
% 2.64/1.01  
% 2.64/1.01  inst_num_of_clauses:                    567
% 2.64/1.01  inst_num_in_passive:                    256
% 2.64/1.01  inst_num_in_active:                     270
% 2.64/1.01  inst_num_in_unprocessed:                41
% 2.64/1.01  inst_num_of_loops:                      270
% 2.64/1.01  inst_num_of_learning_restarts:          0
% 2.64/1.01  inst_num_moves_active_passive:          0
% 2.64/1.01  inst_lit_activity:                      0
% 2.64/1.01  inst_lit_activity_moves:                0
% 2.64/1.01  inst_num_tautologies:                   0
% 2.64/1.01  inst_num_prop_implied:                  0
% 2.64/1.01  inst_num_existing_simplified:           0
% 2.64/1.01  inst_num_eq_res_simplified:             0
% 2.64/1.01  inst_num_child_elim:                    0
% 2.64/1.01  inst_num_of_dismatching_blockings:      0
% 2.64/1.01  inst_num_of_non_proper_insts:           525
% 2.64/1.01  inst_num_of_duplicates:                 0
% 2.64/1.01  inst_inst_num_from_inst_to_res:         0
% 2.64/1.01  inst_dismatching_checking_time:         0.
% 2.64/1.01  
% 2.64/1.01  ------ Resolution
% 2.64/1.01  
% 2.64/1.01  res_num_of_clauses:                     0
% 2.64/1.01  res_num_in_passive:                     0
% 2.64/1.01  res_num_in_active:                      0
% 2.64/1.01  res_num_of_loops:                       79
% 2.64/1.01  res_forward_subset_subsumed:            4
% 2.64/1.01  res_backward_subset_subsumed:           0
% 2.64/1.01  res_forward_subsumed:                   0
% 2.64/1.01  res_backward_subsumed:                  0
% 2.64/1.01  res_forward_subsumption_resolution:     0
% 2.64/1.01  res_backward_subsumption_resolution:    0
% 2.64/1.01  res_clause_to_clause_subsumption:       228
% 2.64/1.01  res_orphan_elimination:                 0
% 2.64/1.01  res_tautology_del:                      1
% 2.64/1.01  res_num_eq_res_simplified:              0
% 2.64/1.01  res_num_sel_changes:                    0
% 2.64/1.01  res_moves_from_active_to_pass:          0
% 2.64/1.01  
% 2.64/1.01  ------ Superposition
% 2.64/1.01  
% 2.64/1.01  sup_time_total:                         0.
% 2.64/1.01  sup_time_generating:                    0.
% 2.64/1.01  sup_time_sim_full:                      0.
% 2.64/1.01  sup_time_sim_immed:                     0.
% 2.64/1.01  
% 2.64/1.01  sup_num_of_clauses:                     73
% 2.64/1.01  sup_num_in_active:                      27
% 2.64/1.01  sup_num_in_passive:                     46
% 2.64/1.01  sup_num_of_loops:                       52
% 2.64/1.01  sup_fw_superposition:                   9
% 2.64/1.01  sup_bw_superposition:                   60
% 2.64/1.01  sup_immediate_simplified:               72
% 2.64/1.01  sup_given_eliminated:                   3
% 2.64/1.01  comparisons_done:                       0
% 2.64/1.01  comparisons_avoided:                    52
% 2.64/1.01  
% 2.64/1.01  ------ Simplifications
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  sim_fw_subset_subsumed:                 0
% 2.64/1.01  sim_bw_subset_subsumed:                 0
% 2.64/1.01  sim_fw_subsumed:                        0
% 2.64/1.01  sim_bw_subsumed:                        0
% 2.64/1.01  sim_fw_subsumption_res:                 0
% 2.64/1.01  sim_bw_subsumption_res:                 0
% 2.64/1.01  sim_tautology_del:                      0
% 2.64/1.01  sim_eq_tautology_del:                   0
% 2.64/1.01  sim_eq_res_simp:                        0
% 2.64/1.01  sim_fw_demodulated:                     0
% 2.64/1.01  sim_bw_demodulated:                     55
% 2.64/1.01  sim_light_normalised:                   81
% 2.64/1.01  sim_joinable_taut:                      0
% 2.64/1.01  sim_joinable_simp:                      0
% 2.64/1.01  sim_ac_normalised:                      0
% 2.64/1.01  sim_smt_subsumption:                    0
% 2.64/1.01  
%------------------------------------------------------------------------------
