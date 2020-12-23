%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:30 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_6418)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(X0))
     => ! [X5] :
          ( m1_subset_1(X5,k1_zfmisc_1(X1))
         => ! [X6] :
              ( m1_subset_1(X6,k1_zfmisc_1(X2))
             => ! [X7] :
                  ( m1_subset_1(X7,k1_zfmisc_1(X3))
                 => ! [X8] :
                      ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                     => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                       => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(X0))
       => ! [X5] :
            ( m1_subset_1(X5,k1_zfmisc_1(X1))
           => ! [X6] :
                ( m1_subset_1(X6,k1_zfmisc_1(X2))
               => ! [X7] :
                    ( m1_subset_1(X7,k1_zfmisc_1(X3))
                   => ! [X8] :
                        ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                       => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                         => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                            & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                            & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                            & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ? [X8] :
          ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
            | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
            | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
            | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
          & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
          & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
     => ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,sK9),X7)
          | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,sK9),X6)
          | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,sK9),X5)
          | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,sK9),X4) )
        & r2_hidden(sK9,k4_zfmisc_1(X4,X5,X6,X7))
        & m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ? [X8] :
              ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
              & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
              & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
          & m1_subset_1(X7,k1_zfmisc_1(X3)) )
     => ( ? [X8] :
            ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),sK8)
              | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
              | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
              | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
            & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,sK8))
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & m1_subset_1(sK8,k1_zfmisc_1(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                    | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                    | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                    | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                  & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                  & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
              & m1_subset_1(X7,k1_zfmisc_1(X3)) )
          & m1_subset_1(X6,k1_zfmisc_1(X2)) )
     => ( ? [X7] :
            ( ? [X8] :
                ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                  | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),sK7)
                  | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                  | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                & r2_hidden(X8,k4_zfmisc_1(X4,X5,sK7,X7))
                & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
            & m1_subset_1(X7,k1_zfmisc_1(X3)) )
        & m1_subset_1(sK7,k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                      | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                      | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),sK6)
                      | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                    & r2_hidden(X8,k4_zfmisc_1(X4,sK6,X6,X7))
                    & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                & m1_subset_1(X7,k1_zfmisc_1(X3)) )
            & m1_subset_1(X6,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK6,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ? [X8] :
                        ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                        & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                        & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                    & m1_subset_1(X7,k1_zfmisc_1(X3)) )
                & m1_subset_1(X6,k1_zfmisc_1(X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X1)) )
        & m1_subset_1(X4,k1_zfmisc_1(X0)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,X8),sK5) )
                      & r2_hidden(X8,k4_zfmisc_1(sK5,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(sK1,sK2,sK3,sK4)) )
                  & m1_subset_1(X7,k1_zfmisc_1(sK4)) )
              & m1_subset_1(X6,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8)
      | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
      | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
      | ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) )
    & r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8))
    & m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4))
    & m1_subset_1(sK8,k1_zfmisc_1(sK4))
    & m1_subset_1(sK7,k1_zfmisc_1(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f16,f26,f25,f24,f23,f22])).

fof(f48,plain,(
    r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f55,plain,(
    r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
            & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
            & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
            & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f49,plain,
    ( ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8)
    | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
    | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
    | ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1653,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1642,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1648,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3046,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1642,c_1648])).

cnf(c_3630,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3046,c_1648])).

cnf(c_3955,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3630,c_1648])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1654,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6804,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3955,c_1654])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1650,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16776,plain,
    ( r1_tarski(X0,k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6804,c_1650])).

cnf(c_18292,plain,
    ( r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_16776])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1641,plain,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1647,plain,
    ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4164,plain,
    ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(sK9)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1641,c_1647])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1646,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4064,plain,
    ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(sK9))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1641,c_1646])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1645,plain,
    ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2940,plain,
    ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1641,c_1645])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1644,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2126,plain,
    ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1641,c_1644])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)
    | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
    | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
    | ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1643,plain,
    ( r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) != iProver_top
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2822,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2126,c_1643])).

cnf(c_25,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1814,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
    | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1815,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top
    | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1814])).

cnf(c_1889,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
    | ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1893,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1889])).

cnf(c_2070,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2074,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) = iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2070])).

cnf(c_2825,plain,
    ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2822,c_25,c_1815,c_1893,c_2074])).

cnf(c_2826,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_2825])).

cnf(c_3792,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2940,c_2826])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2071,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2072,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2071])).

cnf(c_5995,plain,
    ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3792,c_25,c_1815,c_1893,c_2072])).

cnf(c_5996,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_5995])).

cnf(c_6005,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4064,c_5996])).

cnf(c_1890,plain,
    ( ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1891,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1890])).

cnf(c_6008,plain,
    ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6005,c_25,c_1815,c_1891])).

cnf(c_6009,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_6008])).

cnf(c_6017,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4164,c_6009])).

cnf(c_1811,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK8)
    | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6018,plain,
    ( ~ r2_hidden(k2_mcart_1(sK9),sK8)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6017])).

cnf(c_6408,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6017,c_25,c_1812])).

cnf(c_6409,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6408])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1640,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6421,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6409,c_1640])).

cnf(c_1812,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK8) = iProver_top
    | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1811])).

cnf(c_1864,plain,
    ( r2_hidden(k2_mcart_1(sK9),X0)
    | ~ r2_hidden(k2_mcart_1(sK9),sK8)
    | ~ r1_tarski(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1868,plain,
    ( r2_hidden(k2_mcart_1(sK9),X0) = iProver_top
    | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top
    | r1_tarski(sK8,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1864])).

cnf(c_1870,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top
    | r2_hidden(k2_mcart_1(sK9),k1_xboole_0) = iProver_top
    | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1868])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2134,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0))
    | r1_tarski(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2135,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2134])).

cnf(c_2137,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK8,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_2601,plain,
    ( ~ r2_hidden(k2_mcart_1(sK9),X0)
    | ~ r1_tarski(X0,k2_mcart_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2602,plain,
    ( r2_hidden(k2_mcart_1(sK9),X0) != iProver_top
    | r1_tarski(X0,k2_mcart_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2601])).

cnf(c_2604,plain,
    ( r2_hidden(k2_mcart_1(sK9),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_mcart_1(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2602])).

cnf(c_2863,plain,
    ( r1_tarski(k1_xboole_0,k2_mcart_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2866,plain,
    ( r1_tarski(k1_xboole_0,k2_mcart_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2863])).

cnf(c_6465,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6421,c_25,c_1812,c_1870,c_2604,c_2866,c_6418])).

cnf(c_6466,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6465])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1639,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1651,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2245,plain,
    ( r1_tarski(sK7,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_1651])).

cnf(c_6474,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6466,c_2245])).

cnf(c_1649,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3629,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3046,c_1649])).

cnf(c_3938,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),X0) = iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3629,c_1654])).

cnf(c_10731,plain,
    ( r1_tarski(X0,k2_mcart_1(k1_mcart_1(sK9))) != iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3938,c_1650])).

cnf(c_16810,plain,
    ( r1_tarski(sK7,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_10731])).

cnf(c_17231,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6474,c_16810])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1638,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2246,plain,
    ( r1_tarski(sK6,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1651])).

cnf(c_17240,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17231,c_2246])).

cnf(c_3954,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3630,c_1649])).

cnf(c_4239,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),X0) = iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3954,c_1654])).

cnf(c_16115,plain,
    ( r1_tarski(X0,k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4239,c_1650])).

cnf(c_18110,plain,
    ( r1_tarski(sK6,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_16115])).

cnf(c_18117,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17240,c_18110])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1637,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2247,plain,
    ( r1_tarski(sK5,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1637,c_1651])).

cnf(c_18126,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18117,c_2247])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18292,c_18126])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.38/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.00  
% 3.38/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.38/1.00  
% 3.38/1.00  ------  iProver source info
% 3.38/1.00  
% 3.38/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.38/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.38/1.00  git: non_committed_changes: false
% 3.38/1.00  git: last_make_outside_of_git: false
% 3.38/1.00  
% 3.38/1.00  ------ 
% 3.38/1.00  
% 3.38/1.00  ------ Input Options
% 3.38/1.00  
% 3.38/1.00  --out_options                           all
% 3.38/1.00  --tptp_safe_out                         true
% 3.38/1.00  --problem_path                          ""
% 3.38/1.00  --include_path                          ""
% 3.38/1.00  --clausifier                            res/vclausify_rel
% 3.38/1.00  --clausifier_options                    --mode clausify
% 3.38/1.00  --stdin                                 false
% 3.38/1.00  --stats_out                             all
% 3.38/1.00  
% 3.38/1.00  ------ General Options
% 3.38/1.00  
% 3.38/1.00  --fof                                   false
% 3.38/1.00  --time_out_real                         305.
% 3.38/1.00  --time_out_virtual                      -1.
% 3.38/1.00  --symbol_type_check                     false
% 3.38/1.00  --clausify_out                          false
% 3.38/1.00  --sig_cnt_out                           false
% 3.38/1.00  --trig_cnt_out                          false
% 3.38/1.00  --trig_cnt_out_tolerance                1.
% 3.38/1.00  --trig_cnt_out_sk_spl                   false
% 3.38/1.00  --abstr_cl_out                          false
% 3.38/1.00  
% 3.38/1.00  ------ Global Options
% 3.38/1.00  
% 3.38/1.00  --schedule                              default
% 3.38/1.00  --add_important_lit                     false
% 3.38/1.00  --prop_solver_per_cl                    1000
% 3.38/1.00  --min_unsat_core                        false
% 3.38/1.00  --soft_assumptions                      false
% 3.38/1.00  --soft_lemma_size                       3
% 3.38/1.00  --prop_impl_unit_size                   0
% 3.38/1.00  --prop_impl_unit                        []
% 3.38/1.00  --share_sel_clauses                     true
% 3.38/1.00  --reset_solvers                         false
% 3.38/1.00  --bc_imp_inh                            [conj_cone]
% 3.38/1.00  --conj_cone_tolerance                   3.
% 3.38/1.00  --extra_neg_conj                        none
% 3.38/1.00  --large_theory_mode                     true
% 3.38/1.00  --prolific_symb_bound                   200
% 3.38/1.00  --lt_threshold                          2000
% 3.38/1.00  --clause_weak_htbl                      true
% 3.38/1.00  --gc_record_bc_elim                     false
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing Options
% 3.38/1.00  
% 3.38/1.00  --preprocessing_flag                    true
% 3.38/1.00  --time_out_prep_mult                    0.1
% 3.38/1.00  --splitting_mode                        input
% 3.38/1.00  --splitting_grd                         true
% 3.38/1.00  --splitting_cvd                         false
% 3.38/1.00  --splitting_cvd_svl                     false
% 3.38/1.00  --splitting_nvd                         32
% 3.38/1.00  --sub_typing                            true
% 3.38/1.00  --prep_gs_sim                           true
% 3.38/1.00  --prep_unflatten                        true
% 3.38/1.00  --prep_res_sim                          true
% 3.38/1.00  --prep_upred                            true
% 3.38/1.00  --prep_sem_filter                       exhaustive
% 3.38/1.00  --prep_sem_filter_out                   false
% 3.38/1.00  --pred_elim                             true
% 3.38/1.00  --res_sim_input                         true
% 3.38/1.00  --eq_ax_congr_red                       true
% 3.38/1.00  --pure_diseq_elim                       true
% 3.38/1.00  --brand_transform                       false
% 3.38/1.00  --non_eq_to_eq                          false
% 3.38/1.00  --prep_def_merge                        true
% 3.38/1.00  --prep_def_merge_prop_impl              false
% 3.38/1.00  --prep_def_merge_mbd                    true
% 3.38/1.00  --prep_def_merge_tr_red                 false
% 3.38/1.00  --prep_def_merge_tr_cl                  false
% 3.38/1.00  --smt_preprocessing                     true
% 3.38/1.00  --smt_ac_axioms                         fast
% 3.38/1.00  --preprocessed_out                      false
% 3.38/1.00  --preprocessed_stats                    false
% 3.38/1.00  
% 3.38/1.00  ------ Abstraction refinement Options
% 3.38/1.00  
% 3.38/1.00  --abstr_ref                             []
% 3.38/1.00  --abstr_ref_prep                        false
% 3.38/1.00  --abstr_ref_until_sat                   false
% 3.38/1.00  --abstr_ref_sig_restrict                funpre
% 3.38/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/1.00  --abstr_ref_under                       []
% 3.38/1.00  
% 3.38/1.00  ------ SAT Options
% 3.38/1.00  
% 3.38/1.00  --sat_mode                              false
% 3.38/1.00  --sat_fm_restart_options                ""
% 3.38/1.00  --sat_gr_def                            false
% 3.38/1.00  --sat_epr_types                         true
% 3.38/1.00  --sat_non_cyclic_types                  false
% 3.38/1.00  --sat_finite_models                     false
% 3.38/1.00  --sat_fm_lemmas                         false
% 3.38/1.00  --sat_fm_prep                           false
% 3.38/1.00  --sat_fm_uc_incr                        true
% 3.38/1.00  --sat_out_model                         small
% 3.38/1.00  --sat_out_clauses                       false
% 3.38/1.00  
% 3.38/1.00  ------ QBF Options
% 3.38/1.00  
% 3.38/1.00  --qbf_mode                              false
% 3.38/1.00  --qbf_elim_univ                         false
% 3.38/1.00  --qbf_dom_inst                          none
% 3.38/1.00  --qbf_dom_pre_inst                      false
% 3.38/1.00  --qbf_sk_in                             false
% 3.38/1.00  --qbf_pred_elim                         true
% 3.38/1.00  --qbf_split                             512
% 3.38/1.00  
% 3.38/1.00  ------ BMC1 Options
% 3.38/1.00  
% 3.38/1.00  --bmc1_incremental                      false
% 3.38/1.00  --bmc1_axioms                           reachable_all
% 3.38/1.00  --bmc1_min_bound                        0
% 3.38/1.00  --bmc1_max_bound                        -1
% 3.38/1.00  --bmc1_max_bound_default                -1
% 3.38/1.00  --bmc1_symbol_reachability              true
% 3.38/1.00  --bmc1_property_lemmas                  false
% 3.38/1.00  --bmc1_k_induction                      false
% 3.38/1.00  --bmc1_non_equiv_states                 false
% 3.38/1.00  --bmc1_deadlock                         false
% 3.38/1.00  --bmc1_ucm                              false
% 3.38/1.00  --bmc1_add_unsat_core                   none
% 3.38/1.00  --bmc1_unsat_core_children              false
% 3.38/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/1.00  --bmc1_out_stat                         full
% 3.38/1.00  --bmc1_ground_init                      false
% 3.38/1.00  --bmc1_pre_inst_next_state              false
% 3.38/1.00  --bmc1_pre_inst_state                   false
% 3.38/1.00  --bmc1_pre_inst_reach_state             false
% 3.38/1.00  --bmc1_out_unsat_core                   false
% 3.38/1.00  --bmc1_aig_witness_out                  false
% 3.38/1.00  --bmc1_verbose                          false
% 3.38/1.00  --bmc1_dump_clauses_tptp                false
% 3.38/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.38/1.00  --bmc1_dump_file                        -
% 3.38/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.38/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.38/1.00  --bmc1_ucm_extend_mode                  1
% 3.38/1.00  --bmc1_ucm_init_mode                    2
% 3.38/1.00  --bmc1_ucm_cone_mode                    none
% 3.38/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.38/1.00  --bmc1_ucm_relax_model                  4
% 3.38/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.38/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/1.00  --bmc1_ucm_layered_model                none
% 3.38/1.00  --bmc1_ucm_max_lemma_size               10
% 3.38/1.00  
% 3.38/1.00  ------ AIG Options
% 3.38/1.00  
% 3.38/1.00  --aig_mode                              false
% 3.38/1.00  
% 3.38/1.00  ------ Instantiation Options
% 3.38/1.00  
% 3.38/1.00  --instantiation_flag                    true
% 3.38/1.00  --inst_sos_flag                         false
% 3.38/1.00  --inst_sos_phase                        true
% 3.38/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel_side                     num_symb
% 3.38/1.00  --inst_solver_per_active                1400
% 3.38/1.00  --inst_solver_calls_frac                1.
% 3.38/1.00  --inst_passive_queue_type               priority_queues
% 3.38/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/1.00  --inst_passive_queues_freq              [25;2]
% 3.38/1.00  --inst_dismatching                      true
% 3.38/1.00  --inst_eager_unprocessed_to_passive     true
% 3.38/1.00  --inst_prop_sim_given                   true
% 3.38/1.00  --inst_prop_sim_new                     false
% 3.38/1.00  --inst_subs_new                         false
% 3.38/1.00  --inst_eq_res_simp                      false
% 3.38/1.00  --inst_subs_given                       false
% 3.38/1.00  --inst_orphan_elimination               true
% 3.38/1.00  --inst_learning_loop_flag               true
% 3.38/1.00  --inst_learning_start                   3000
% 3.38/1.00  --inst_learning_factor                  2
% 3.38/1.00  --inst_start_prop_sim_after_learn       3
% 3.38/1.00  --inst_sel_renew                        solver
% 3.38/1.00  --inst_lit_activity_flag                true
% 3.38/1.00  --inst_restr_to_given                   false
% 3.38/1.00  --inst_activity_threshold               500
% 3.38/1.00  --inst_out_proof                        true
% 3.38/1.00  
% 3.38/1.00  ------ Resolution Options
% 3.38/1.00  
% 3.38/1.00  --resolution_flag                       true
% 3.38/1.00  --res_lit_sel                           adaptive
% 3.38/1.00  --res_lit_sel_side                      none
% 3.38/1.00  --res_ordering                          kbo
% 3.38/1.00  --res_to_prop_solver                    active
% 3.38/1.00  --res_prop_simpl_new                    false
% 3.38/1.00  --res_prop_simpl_given                  true
% 3.38/1.00  --res_passive_queue_type                priority_queues
% 3.38/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/1.00  --res_passive_queues_freq               [15;5]
% 3.38/1.00  --res_forward_subs                      full
% 3.38/1.00  --res_backward_subs                     full
% 3.38/1.00  --res_forward_subs_resolution           true
% 3.38/1.00  --res_backward_subs_resolution          true
% 3.38/1.00  --res_orphan_elimination                true
% 3.38/1.00  --res_time_limit                        2.
% 3.38/1.00  --res_out_proof                         true
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Options
% 3.38/1.00  
% 3.38/1.00  --superposition_flag                    true
% 3.38/1.00  --sup_passive_queue_type                priority_queues
% 3.38/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.38/1.00  --demod_completeness_check              fast
% 3.38/1.00  --demod_use_ground                      true
% 3.38/1.00  --sup_to_prop_solver                    passive
% 3.38/1.00  --sup_prop_simpl_new                    true
% 3.38/1.00  --sup_prop_simpl_given                  true
% 3.38/1.00  --sup_fun_splitting                     false
% 3.38/1.00  --sup_smt_interval                      50000
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Simplification Setup
% 3.38/1.00  
% 3.38/1.00  --sup_indices_passive                   []
% 3.38/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_full_bw                           [BwDemod]
% 3.38/1.00  --sup_immed_triv                        [TrivRules]
% 3.38/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_immed_bw_main                     []
% 3.38/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/1.00  
% 3.38/1.00  ------ Combination Options
% 3.38/1.00  
% 3.38/1.00  --comb_res_mult                         3
% 3.38/1.00  --comb_sup_mult                         2
% 3.38/1.00  --comb_inst_mult                        10
% 3.38/1.00  
% 3.38/1.00  ------ Debug Options
% 3.38/1.00  
% 3.38/1.00  --dbg_backtrace                         false
% 3.38/1.00  --dbg_dump_prop_clauses                 false
% 3.38/1.00  --dbg_dump_prop_clauses_file            -
% 3.38/1.00  --dbg_out_stat                          false
% 3.38/1.00  ------ Parsing...
% 3.38/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.38/1.00  ------ Proving...
% 3.38/1.00  ------ Problem Properties 
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  clauses                                 20
% 3.38/1.00  conjectures                             7
% 3.38/1.00  EPR                                     3
% 3.38/1.00  Horn                                    15
% 3.38/1.00  unary                                   7
% 3.38/1.00  binary                                  7
% 3.38/1.00  lits                                    52
% 3.38/1.00  lits eq                                 20
% 3.38/1.00  fd_pure                                 0
% 3.38/1.00  fd_pseudo                               0
% 3.38/1.00  fd_cond                                 4
% 3.38/1.00  fd_pseudo_cond                          0
% 3.38/1.00  AC symbols                              0
% 3.38/1.00  
% 3.38/1.00  ------ Schedule dynamic 5 is on 
% 3.38/1.00  
% 3.38/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  ------ 
% 3.38/1.00  Current options:
% 3.38/1.00  ------ 
% 3.38/1.00  
% 3.38/1.00  ------ Input Options
% 3.38/1.00  
% 3.38/1.00  --out_options                           all
% 3.38/1.00  --tptp_safe_out                         true
% 3.38/1.00  --problem_path                          ""
% 3.38/1.00  --include_path                          ""
% 3.38/1.00  --clausifier                            res/vclausify_rel
% 3.38/1.00  --clausifier_options                    --mode clausify
% 3.38/1.00  --stdin                                 false
% 3.38/1.00  --stats_out                             all
% 3.38/1.00  
% 3.38/1.00  ------ General Options
% 3.38/1.00  
% 3.38/1.00  --fof                                   false
% 3.38/1.00  --time_out_real                         305.
% 3.38/1.00  --time_out_virtual                      -1.
% 3.38/1.00  --symbol_type_check                     false
% 3.38/1.00  --clausify_out                          false
% 3.38/1.00  --sig_cnt_out                           false
% 3.38/1.00  --trig_cnt_out                          false
% 3.38/1.00  --trig_cnt_out_tolerance                1.
% 3.38/1.00  --trig_cnt_out_sk_spl                   false
% 3.38/1.00  --abstr_cl_out                          false
% 3.38/1.00  
% 3.38/1.00  ------ Global Options
% 3.38/1.00  
% 3.38/1.00  --schedule                              default
% 3.38/1.00  --add_important_lit                     false
% 3.38/1.00  --prop_solver_per_cl                    1000
% 3.38/1.00  --min_unsat_core                        false
% 3.38/1.00  --soft_assumptions                      false
% 3.38/1.00  --soft_lemma_size                       3
% 3.38/1.00  --prop_impl_unit_size                   0
% 3.38/1.00  --prop_impl_unit                        []
% 3.38/1.00  --share_sel_clauses                     true
% 3.38/1.00  --reset_solvers                         false
% 3.38/1.00  --bc_imp_inh                            [conj_cone]
% 3.38/1.00  --conj_cone_tolerance                   3.
% 3.38/1.00  --extra_neg_conj                        none
% 3.38/1.00  --large_theory_mode                     true
% 3.38/1.00  --prolific_symb_bound                   200
% 3.38/1.00  --lt_threshold                          2000
% 3.38/1.00  --clause_weak_htbl                      true
% 3.38/1.00  --gc_record_bc_elim                     false
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing Options
% 3.38/1.00  
% 3.38/1.00  --preprocessing_flag                    true
% 3.38/1.00  --time_out_prep_mult                    0.1
% 3.38/1.00  --splitting_mode                        input
% 3.38/1.00  --splitting_grd                         true
% 3.38/1.00  --splitting_cvd                         false
% 3.38/1.00  --splitting_cvd_svl                     false
% 3.38/1.00  --splitting_nvd                         32
% 3.38/1.00  --sub_typing                            true
% 3.38/1.00  --prep_gs_sim                           true
% 3.38/1.00  --prep_unflatten                        true
% 3.38/1.00  --prep_res_sim                          true
% 3.38/1.00  --prep_upred                            true
% 3.38/1.00  --prep_sem_filter                       exhaustive
% 3.38/1.00  --prep_sem_filter_out                   false
% 3.38/1.00  --pred_elim                             true
% 3.38/1.00  --res_sim_input                         true
% 3.38/1.00  --eq_ax_congr_red                       true
% 3.38/1.00  --pure_diseq_elim                       true
% 3.38/1.00  --brand_transform                       false
% 3.38/1.00  --non_eq_to_eq                          false
% 3.38/1.00  --prep_def_merge                        true
% 3.38/1.00  --prep_def_merge_prop_impl              false
% 3.38/1.00  --prep_def_merge_mbd                    true
% 3.38/1.00  --prep_def_merge_tr_red                 false
% 3.38/1.00  --prep_def_merge_tr_cl                  false
% 3.38/1.00  --smt_preprocessing                     true
% 3.38/1.00  --smt_ac_axioms                         fast
% 3.38/1.00  --preprocessed_out                      false
% 3.38/1.00  --preprocessed_stats                    false
% 3.38/1.00  
% 3.38/1.00  ------ Abstraction refinement Options
% 3.38/1.00  
% 3.38/1.00  --abstr_ref                             []
% 3.38/1.00  --abstr_ref_prep                        false
% 3.38/1.00  --abstr_ref_until_sat                   false
% 3.38/1.00  --abstr_ref_sig_restrict                funpre
% 3.38/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/1.00  --abstr_ref_under                       []
% 3.38/1.00  
% 3.38/1.00  ------ SAT Options
% 3.38/1.00  
% 3.38/1.00  --sat_mode                              false
% 3.38/1.00  --sat_fm_restart_options                ""
% 3.38/1.00  --sat_gr_def                            false
% 3.38/1.00  --sat_epr_types                         true
% 3.38/1.00  --sat_non_cyclic_types                  false
% 3.38/1.00  --sat_finite_models                     false
% 3.38/1.00  --sat_fm_lemmas                         false
% 3.38/1.00  --sat_fm_prep                           false
% 3.38/1.00  --sat_fm_uc_incr                        true
% 3.38/1.00  --sat_out_model                         small
% 3.38/1.00  --sat_out_clauses                       false
% 3.38/1.00  
% 3.38/1.00  ------ QBF Options
% 3.38/1.00  
% 3.38/1.00  --qbf_mode                              false
% 3.38/1.00  --qbf_elim_univ                         false
% 3.38/1.00  --qbf_dom_inst                          none
% 3.38/1.00  --qbf_dom_pre_inst                      false
% 3.38/1.00  --qbf_sk_in                             false
% 3.38/1.00  --qbf_pred_elim                         true
% 3.38/1.00  --qbf_split                             512
% 3.38/1.00  
% 3.38/1.00  ------ BMC1 Options
% 3.38/1.00  
% 3.38/1.00  --bmc1_incremental                      false
% 3.38/1.00  --bmc1_axioms                           reachable_all
% 3.38/1.00  --bmc1_min_bound                        0
% 3.38/1.00  --bmc1_max_bound                        -1
% 3.38/1.00  --bmc1_max_bound_default                -1
% 3.38/1.00  --bmc1_symbol_reachability              true
% 3.38/1.00  --bmc1_property_lemmas                  false
% 3.38/1.00  --bmc1_k_induction                      false
% 3.38/1.00  --bmc1_non_equiv_states                 false
% 3.38/1.00  --bmc1_deadlock                         false
% 3.38/1.00  --bmc1_ucm                              false
% 3.38/1.00  --bmc1_add_unsat_core                   none
% 3.38/1.00  --bmc1_unsat_core_children              false
% 3.38/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/1.00  --bmc1_out_stat                         full
% 3.38/1.00  --bmc1_ground_init                      false
% 3.38/1.00  --bmc1_pre_inst_next_state              false
% 3.38/1.00  --bmc1_pre_inst_state                   false
% 3.38/1.00  --bmc1_pre_inst_reach_state             false
% 3.38/1.00  --bmc1_out_unsat_core                   false
% 3.38/1.00  --bmc1_aig_witness_out                  false
% 3.38/1.00  --bmc1_verbose                          false
% 3.38/1.00  --bmc1_dump_clauses_tptp                false
% 3.38/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.38/1.00  --bmc1_dump_file                        -
% 3.38/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.38/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.38/1.00  --bmc1_ucm_extend_mode                  1
% 3.38/1.00  --bmc1_ucm_init_mode                    2
% 3.38/1.00  --bmc1_ucm_cone_mode                    none
% 3.38/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.38/1.00  --bmc1_ucm_relax_model                  4
% 3.38/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.38/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/1.00  --bmc1_ucm_layered_model                none
% 3.38/1.00  --bmc1_ucm_max_lemma_size               10
% 3.38/1.00  
% 3.38/1.00  ------ AIG Options
% 3.38/1.00  
% 3.38/1.00  --aig_mode                              false
% 3.38/1.00  
% 3.38/1.00  ------ Instantiation Options
% 3.38/1.00  
% 3.38/1.00  --instantiation_flag                    true
% 3.38/1.00  --inst_sos_flag                         false
% 3.38/1.00  --inst_sos_phase                        true
% 3.38/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel_side                     none
% 3.38/1.00  --inst_solver_per_active                1400
% 3.38/1.00  --inst_solver_calls_frac                1.
% 3.38/1.00  --inst_passive_queue_type               priority_queues
% 3.38/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/1.00  --inst_passive_queues_freq              [25;2]
% 3.38/1.00  --inst_dismatching                      true
% 3.38/1.00  --inst_eager_unprocessed_to_passive     true
% 3.38/1.00  --inst_prop_sim_given                   true
% 3.38/1.00  --inst_prop_sim_new                     false
% 3.38/1.00  --inst_subs_new                         false
% 3.38/1.00  --inst_eq_res_simp                      false
% 3.38/1.00  --inst_subs_given                       false
% 3.38/1.00  --inst_orphan_elimination               true
% 3.38/1.00  --inst_learning_loop_flag               true
% 3.38/1.00  --inst_learning_start                   3000
% 3.38/1.00  --inst_learning_factor                  2
% 3.38/1.00  --inst_start_prop_sim_after_learn       3
% 3.38/1.00  --inst_sel_renew                        solver
% 3.38/1.00  --inst_lit_activity_flag                true
% 3.38/1.00  --inst_restr_to_given                   false
% 3.38/1.00  --inst_activity_threshold               500
% 3.38/1.00  --inst_out_proof                        true
% 3.38/1.00  
% 3.38/1.00  ------ Resolution Options
% 3.38/1.00  
% 3.38/1.00  --resolution_flag                       false
% 3.38/1.00  --res_lit_sel                           adaptive
% 3.38/1.00  --res_lit_sel_side                      none
% 3.38/1.00  --res_ordering                          kbo
% 3.38/1.00  --res_to_prop_solver                    active
% 3.38/1.00  --res_prop_simpl_new                    false
% 3.38/1.00  --res_prop_simpl_given                  true
% 3.38/1.00  --res_passive_queue_type                priority_queues
% 3.38/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/1.00  --res_passive_queues_freq               [15;5]
% 3.38/1.00  --res_forward_subs                      full
% 3.38/1.00  --res_backward_subs                     full
% 3.38/1.00  --res_forward_subs_resolution           true
% 3.38/1.00  --res_backward_subs_resolution          true
% 3.38/1.00  --res_orphan_elimination                true
% 3.38/1.00  --res_time_limit                        2.
% 3.38/1.00  --res_out_proof                         true
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Options
% 3.38/1.00  
% 3.38/1.00  --superposition_flag                    true
% 3.38/1.00  --sup_passive_queue_type                priority_queues
% 3.38/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.38/1.00  --demod_completeness_check              fast
% 3.38/1.00  --demod_use_ground                      true
% 3.38/1.00  --sup_to_prop_solver                    passive
% 3.38/1.00  --sup_prop_simpl_new                    true
% 3.38/1.00  --sup_prop_simpl_given                  true
% 3.38/1.00  --sup_fun_splitting                     false
% 3.38/1.00  --sup_smt_interval                      50000
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Simplification Setup
% 3.38/1.00  
% 3.38/1.00  --sup_indices_passive                   []
% 3.38/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_full_bw                           [BwDemod]
% 3.38/1.00  --sup_immed_triv                        [TrivRules]
% 3.38/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_immed_bw_main                     []
% 3.38/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/1.00  
% 3.38/1.00  ------ Combination Options
% 3.38/1.00  
% 3.38/1.00  --comb_res_mult                         3
% 3.38/1.00  --comb_sup_mult                         2
% 3.38/1.00  --comb_inst_mult                        10
% 3.38/1.00  
% 3.38/1.00  ------ Debug Options
% 3.38/1.00  
% 3.38/1.00  --dbg_backtrace                         false
% 3.38/1.00  --dbg_dump_prop_clauses                 false
% 3.38/1.00  --dbg_dump_prop_clauses_file            -
% 3.38/1.00  --dbg_out_stat                          false
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  ------ Proving...
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  % SZS status Theorem for theBenchmark.p
% 3.38/1.00  
% 3.38/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.38/1.00  
% 3.38/1.00  fof(f2,axiom,(
% 3.38/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f31,plain,(
% 3.38/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f2])).
% 3.38/1.00  
% 3.38/1.00  fof(f9,conjecture,(
% 3.38/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f10,negated_conjecture,(
% 3.38/1.00    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 3.38/1.00    inference(negated_conjecture,[],[f9])).
% 3.38/1.00  
% 3.38/1.00  fof(f15,plain,(
% 3.38/1.00    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 3.38/1.00    inference(ennf_transformation,[],[f10])).
% 3.38/1.00  
% 3.38/1.00  fof(f16,plain,(
% 3.38/1.00    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 3.38/1.00    inference(flattening,[],[f15])).
% 3.38/1.00  
% 3.38/1.00  fof(f26,plain,(
% 3.38/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) => ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,sK9),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,sK9),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,sK9),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,sK9),X4)) & r2_hidden(sK9,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)))) )),
% 3.38/1.00    introduced(choice_axiom,[])).
% 3.38/1.00  
% 3.38/1.00  fof(f25,plain,(
% 3.38/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),sK8) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,sK8)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(sK8,k1_zfmisc_1(X3)))) )),
% 3.38/1.00    introduced(choice_axiom,[])).
% 3.38/1.00  
% 3.38/1.00  fof(f24,plain,(
% 3.38/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),sK7) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,sK7,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(sK7,k1_zfmisc_1(X2)))) )),
% 3.38/1.00    introduced(choice_axiom,[])).
% 3.38/1.00  
% 3.38/1.00  fof(f23,plain,(
% 3.38/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),sK6) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,sK6,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(sK6,k1_zfmisc_1(X1)))) )),
% 3.38/1.00    introduced(choice_axiom,[])).
% 3.38/1.00  
% 3.38/1.00  fof(f22,plain,(
% 3.38/1.00    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,X8),X7) | ~r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,X8),X6) | ~r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,X8),X5) | ~r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,X8),sK5)) & r2_hidden(X8,k4_zfmisc_1(sK5,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK1,sK2,sK3,sK4))) & m1_subset_1(X7,k1_zfmisc_1(sK4))) & m1_subset_1(X6,k1_zfmisc_1(sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1)))),
% 3.38/1.00    introduced(choice_axiom,[])).
% 3.38/1.00  
% 3.38/1.00  fof(f27,plain,(
% 3.38/1.00    (((((~r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) | ~r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) | ~r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) | ~r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)) & r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) & m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4))) & m1_subset_1(sK8,k1_zfmisc_1(sK4))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 3.38/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f16,f26,f25,f24,f23,f22])).
% 3.38/1.00  
% 3.38/1.00  fof(f48,plain,(
% 3.38/1.00    r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8))),
% 3.38/1.00    inference(cnf_transformation,[],[f27])).
% 3.38/1.00  
% 3.38/1.00  fof(f6,axiom,(
% 3.38/1.00    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f36,plain,(
% 3.38/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f6])).
% 3.38/1.00  
% 3.38/1.00  fof(f5,axiom,(
% 3.38/1.00    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f35,plain,(
% 3.38/1.00    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f5])).
% 3.38/1.00  
% 3.38/1.00  fof(f50,plain,(
% 3.38/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.38/1.00    inference(definition_unfolding,[],[f36,f35])).
% 3.38/1.00  
% 3.38/1.00  fof(f55,plain,(
% 3.38/1.00    r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8))),
% 3.38/1.00    inference(definition_unfolding,[],[f48,f50])).
% 3.38/1.00  
% 3.38/1.00  fof(f7,axiom,(
% 3.38/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f13,plain,(
% 3.38/1.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.38/1.00    inference(ennf_transformation,[],[f7])).
% 3.38/1.00  
% 3.38/1.00  fof(f37,plain,(
% 3.38/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.38/1.00    inference(cnf_transformation,[],[f13])).
% 3.38/1.00  
% 3.38/1.00  fof(f1,axiom,(
% 3.38/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f11,plain,(
% 3.38/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.38/1.00    inference(ennf_transformation,[],[f1])).
% 3.38/1.00  
% 3.38/1.00  fof(f17,plain,(
% 3.38/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.38/1.00    inference(nnf_transformation,[],[f11])).
% 3.38/1.00  
% 3.38/1.00  fof(f18,plain,(
% 3.38/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.38/1.01    inference(rectify,[],[f17])).
% 3.38/1.01  
% 3.38/1.01  fof(f19,plain,(
% 3.38/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.38/1.01    introduced(choice_axiom,[])).
% 3.38/1.01  
% 3.38/1.01  fof(f20,plain,(
% 3.38/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.38/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 3.38/1.01  
% 3.38/1.01  fof(f28,plain,(
% 3.38/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.38/1.01    inference(cnf_transformation,[],[f20])).
% 3.38/1.01  
% 3.38/1.01  fof(f4,axiom,(
% 3.38/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f12,plain,(
% 3.38/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.38/1.01    inference(ennf_transformation,[],[f4])).
% 3.38/1.01  
% 3.38/1.01  fof(f34,plain,(
% 3.38/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.38/1.01    inference(cnf_transformation,[],[f12])).
% 3.38/1.01  
% 3.38/1.01  fof(f47,plain,(
% 3.38/1.01    m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 3.38/1.01    inference(cnf_transformation,[],[f27])).
% 3.38/1.01  
% 3.38/1.01  fof(f56,plain,(
% 3.38/1.01    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 3.38/1.01    inference(definition_unfolding,[],[f47,f50])).
% 3.38/1.01  
% 3.38/1.01  fof(f8,axiom,(
% 3.38/1.01    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f14,plain,(
% 3.38/1.01    ! [X0,X1,X2,X3] : (! [X4] : ((k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.38/1.01    inference(ennf_transformation,[],[f8])).
% 3.38/1.01  
% 3.38/1.01  fof(f42,plain,(
% 3.38/1.01    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.38/1.01    inference(cnf_transformation,[],[f14])).
% 3.38/1.01  
% 3.38/1.01  fof(f51,plain,(
% 3.38/1.01    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.38/1.01    inference(definition_unfolding,[],[f42,f50])).
% 3.38/1.01  
% 3.38/1.01  fof(f41,plain,(
% 3.38/1.01    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.38/1.01    inference(cnf_transformation,[],[f14])).
% 3.38/1.01  
% 3.38/1.01  fof(f52,plain,(
% 3.38/1.01    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.38/1.01    inference(definition_unfolding,[],[f41,f50])).
% 3.38/1.01  
% 3.38/1.01  fof(f40,plain,(
% 3.38/1.01    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.38/1.01    inference(cnf_transformation,[],[f14])).
% 3.38/1.01  
% 3.38/1.01  fof(f53,plain,(
% 3.38/1.01    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.38/1.01    inference(definition_unfolding,[],[f40,f50])).
% 3.38/1.01  
% 3.38/1.01  fof(f39,plain,(
% 3.38/1.01    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.38/1.01    inference(cnf_transformation,[],[f14])).
% 3.38/1.01  
% 3.38/1.01  fof(f54,plain,(
% 3.38/1.01    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.38/1.01    inference(definition_unfolding,[],[f39,f50])).
% 3.38/1.01  
% 3.38/1.01  fof(f49,plain,(
% 3.38/1.01    ~r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) | ~r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) | ~r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) | ~r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)),
% 3.38/1.01    inference(cnf_transformation,[],[f27])).
% 3.38/1.01  
% 3.38/1.01  fof(f38,plain,(
% 3.38/1.01    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.38/1.01    inference(cnf_transformation,[],[f13])).
% 3.38/1.01  
% 3.38/1.01  fof(f46,plain,(
% 3.38/1.01    m1_subset_1(sK8,k1_zfmisc_1(sK4))),
% 3.38/1.01    inference(cnf_transformation,[],[f27])).
% 3.38/1.01  
% 3.38/1.01  fof(f3,axiom,(
% 3.38/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.38/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.01  
% 3.38/1.01  fof(f21,plain,(
% 3.38/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.38/1.01    inference(nnf_transformation,[],[f3])).
% 3.38/1.01  
% 3.38/1.01  fof(f32,plain,(
% 3.38/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.38/1.01    inference(cnf_transformation,[],[f21])).
% 3.38/1.01  
% 3.38/1.01  fof(f45,plain,(
% 3.38/1.01    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 3.38/1.01    inference(cnf_transformation,[],[f27])).
% 3.38/1.01  
% 3.38/1.01  fof(f44,plain,(
% 3.38/1.01    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 3.38/1.01    inference(cnf_transformation,[],[f27])).
% 3.38/1.01  
% 3.38/1.01  fof(f43,plain,(
% 3.38/1.01    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 3.38/1.01    inference(cnf_transformation,[],[f27])).
% 3.38/1.01  
% 3.38/1.01  cnf(c_3,plain,
% 3.38/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.38/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1653,plain,
% 3.38/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_14,negated_conjecture,
% 3.38/1.01      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
% 3.38/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1642,plain,
% 3.38/1.01      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_8,plain,
% 3.38/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.38/1.01      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.38/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1648,plain,
% 3.38/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.38/1.01      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_3046,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_1642,c_1648]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_3630,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_3046,c_1648]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_3955,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_3630,c_1648]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2,plain,
% 3.38/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.38/1.01      inference(cnf_transformation,[],[f28]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1654,plain,
% 3.38/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.38/1.01      | r2_hidden(X0,X2) = iProver_top
% 3.38/1.01      | r1_tarski(X1,X2) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6804,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),X0) = iProver_top
% 3.38/1.01      | r1_tarski(sK5,X0) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_3955,c_1654]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6,plain,
% 3.38/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.38/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1650,plain,
% 3.38/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.38/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_16776,plain,
% 3.38/1.01      ( r1_tarski(X0,k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))) != iProver_top
% 3.38/1.01      | r1_tarski(sK5,X0) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_6804,c_1650]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_18292,plain,
% 3.38/1.01      ( r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_1653,c_16776]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_15,negated_conjecture,
% 3.38/1.01      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
% 3.38/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1641,plain,
% 3.38/1.01      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_9,plain,
% 3.38/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.38/1.01      | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
% 3.38/1.01      | k1_xboole_0 = X4
% 3.38/1.01      | k1_xboole_0 = X3
% 3.38/1.01      | k1_xboole_0 = X2
% 3.38/1.01      | k1_xboole_0 = X1 ),
% 3.38/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1647,plain,
% 3.38/1.01      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
% 3.38/1.01      | k1_xboole_0 = X1
% 3.38/1.01      | k1_xboole_0 = X2
% 3.38/1.01      | k1_xboole_0 = X0
% 3.38/1.01      | k1_xboole_0 = X3
% 3.38/1.01      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_4164,plain,
% 3.38/1.01      ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(sK9)
% 3.38/1.01      | sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0 ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_1641,c_1647]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_10,plain,
% 3.38/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.38/1.01      | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.38/1.01      | k1_xboole_0 = X4
% 3.38/1.01      | k1_xboole_0 = X3
% 3.38/1.01      | k1_xboole_0 = X2
% 3.38/1.01      | k1_xboole_0 = X1 ),
% 3.38/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1646,plain,
% 3.38/1.01      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
% 3.38/1.01      | k1_xboole_0 = X1
% 3.38/1.01      | k1_xboole_0 = X2
% 3.38/1.01      | k1_xboole_0 = X0
% 3.38/1.01      | k1_xboole_0 = X3
% 3.38/1.01      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_4064,plain,
% 3.38/1.01      ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(sK9))
% 3.38/1.01      | sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0 ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_1641,c_1646]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_11,plain,
% 3.38/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.38/1.01      | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 3.38/1.01      | k1_xboole_0 = X4
% 3.38/1.01      | k1_xboole_0 = X3
% 3.38/1.01      | k1_xboole_0 = X2
% 3.38/1.01      | k1_xboole_0 = X1 ),
% 3.38/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1645,plain,
% 3.38/1.01      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 3.38/1.01      | k1_xboole_0 = X1
% 3.38/1.01      | k1_xboole_0 = X2
% 3.38/1.01      | k1_xboole_0 = X0
% 3.38/1.01      | k1_xboole_0 = X3
% 3.38/1.01      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2940,plain,
% 3.38/1.01      ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 3.38/1.01      | sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0 ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_1641,c_1645]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_12,plain,
% 3.38/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.38/1.01      | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 3.38/1.01      | k1_xboole_0 = X4
% 3.38/1.01      | k1_xboole_0 = X3
% 3.38/1.01      | k1_xboole_0 = X2
% 3.38/1.01      | k1_xboole_0 = X1 ),
% 3.38/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1644,plain,
% 3.38/1.01      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 3.38/1.01      | k1_xboole_0 = X1
% 3.38/1.01      | k1_xboole_0 = X2
% 3.38/1.01      | k1_xboole_0 = X0
% 3.38/1.01      | k1_xboole_0 = X3
% 3.38/1.01      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2126,plain,
% 3.38/1.01      ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 3.38/1.01      | sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0 ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_1641,c_1644]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_13,negated_conjecture,
% 3.38/1.01      ( ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)
% 3.38/1.01      | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
% 3.38/1.01      | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
% 3.38/1.01      | ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) ),
% 3.38/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1643,plain,
% 3.38/1.01      ( r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) != iProver_top
% 3.38/1.01      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 3.38/1.01      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.38/1.01      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2822,plain,
% 3.38/1.01      ( sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 3.38/1.01      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.38/1.01      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.38/1.01      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_2126,c_1643]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_25,plain,
% 3.38/1.01      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1814,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
% 3.38/1.01      | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1815,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top
% 3.38/1.01      | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_1814]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1889,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
% 3.38/1.01      | ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1893,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top
% 3.38/1.01      | r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_1889]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2070,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5)
% 3.38/1.01      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2074,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) = iProver_top
% 3.38/1.01      | r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_2070]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2825,plain,
% 3.38/1.01      ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.38/1.01      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.38/1.01      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK4 = k1_xboole_0 ),
% 3.38/1.01      inference(global_propositional_subsumption,
% 3.38/1.01                [status(thm)],
% 3.38/1.01                [c_2822,c_25,c_1815,c_1893,c_2074]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2826,plain,
% 3.38/1.01      ( sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 3.38/1.01      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.38/1.01      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
% 3.38/1.01      inference(renaming,[status(thm)],[c_2825]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_3792,plain,
% 3.38/1.01      ( sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.38/1.01      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.38/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_2940,c_2826]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_7,plain,
% 3.38/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.38/1.01      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.38/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2071,plain,
% 3.38/1.01      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
% 3.38/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2072,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.38/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_2071]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_5995,plain,
% 3.38/1.01      ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.38/1.01      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK4 = k1_xboole_0 ),
% 3.38/1.01      inference(global_propositional_subsumption,
% 3.38/1.01                [status(thm)],
% 3.38/1.01                [c_3792,c_25,c_1815,c_1893,c_2072]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_5996,plain,
% 3.38/1.01      ( sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.38/1.01      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
% 3.38/1.01      inference(renaming,[status(thm)],[c_5995]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6005,plain,
% 3.38/1.01      ( sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.38/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_4064,c_5996]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1890,plain,
% 3.38/1.01      ( ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
% 3.38/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1891,plain,
% 3.38/1.01      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top
% 3.38/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_1890]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6008,plain,
% 3.38/1.01      ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK4 = k1_xboole_0 ),
% 3.38/1.01      inference(global_propositional_subsumption,
% 3.38/1.01                [status(thm)],
% 3.38/1.01                [c_6005,c_25,c_1815,c_1891]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6009,plain,
% 3.38/1.01      ( sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
% 3.38/1.01      inference(renaming,[status(thm)],[c_6008]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6017,plain,
% 3.38/1.01      ( sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_4164,c_6009]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1811,plain,
% 3.38/1.01      ( r2_hidden(k2_mcart_1(sK9),sK8)
% 3.38/1.01      | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6018,plain,
% 3.38/1.01      ( ~ r2_hidden(k2_mcart_1(sK9),sK8)
% 3.38/1.01      | sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0 ),
% 3.38/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6017]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6408,plain,
% 3.38/1.01      ( sK1 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK4 = k1_xboole_0 ),
% 3.38/1.01      inference(global_propositional_subsumption,
% 3.38/1.01                [status(thm)],
% 3.38/1.01                [c_6017,c_25,c_1812]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6409,plain,
% 3.38/1.01      ( sK4 = k1_xboole_0
% 3.38/1.01      | sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0 ),
% 3.38/1.01      inference(renaming,[status(thm)],[c_6408]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_16,negated_conjecture,
% 3.38/1.01      ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
% 3.38/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1640,plain,
% 3.38/1.01      ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6421,plain,
% 3.38/1.01      ( sK3 = k1_xboole_0
% 3.38/1.01      | sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_6409,c_1640]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1812,plain,
% 3.38/1.01      ( r2_hidden(k2_mcart_1(sK9),sK8) = iProver_top
% 3.38/1.01      | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_1811]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1864,plain,
% 3.38/1.01      ( r2_hidden(k2_mcart_1(sK9),X0)
% 3.38/1.01      | ~ r2_hidden(k2_mcart_1(sK9),sK8)
% 3.38/1.01      | ~ r1_tarski(sK8,X0) ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1868,plain,
% 3.38/1.01      ( r2_hidden(k2_mcart_1(sK9),X0) = iProver_top
% 3.38/1.01      | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top
% 3.38/1.01      | r1_tarski(sK8,X0) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_1864]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1870,plain,
% 3.38/1.01      ( r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top
% 3.38/1.01      | r2_hidden(k2_mcart_1(sK9),k1_xboole_0) = iProver_top
% 3.38/1.01      | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_1868]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_5,plain,
% 3.38/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.38/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2134,plain,
% 3.38/1.01      ( ~ m1_subset_1(sK8,k1_zfmisc_1(X0)) | r1_tarski(sK8,X0) ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2135,plain,
% 3.38/1.01      ( m1_subset_1(sK8,k1_zfmisc_1(X0)) != iProver_top
% 3.38/1.01      | r1_tarski(sK8,X0) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_2134]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2137,plain,
% 3.38/1.01      ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.38/1.01      | r1_tarski(sK8,k1_xboole_0) = iProver_top ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_2135]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2601,plain,
% 3.38/1.01      ( ~ r2_hidden(k2_mcart_1(sK9),X0)
% 3.38/1.01      | ~ r1_tarski(X0,k2_mcart_1(sK9)) ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2602,plain,
% 3.38/1.01      ( r2_hidden(k2_mcart_1(sK9),X0) != iProver_top
% 3.38/1.01      | r1_tarski(X0,k2_mcart_1(sK9)) != iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_2601]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2604,plain,
% 3.38/1.01      ( r2_hidden(k2_mcart_1(sK9),k1_xboole_0) != iProver_top
% 3.38/1.01      | r1_tarski(k1_xboole_0,k2_mcart_1(sK9)) != iProver_top ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_2602]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2863,plain,
% 3.38/1.01      ( r1_tarski(k1_xboole_0,k2_mcart_1(sK9)) ),
% 3.38/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2866,plain,
% 3.38/1.01      ( r1_tarski(k1_xboole_0,k2_mcart_1(sK9)) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_2863]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6465,plain,
% 3.38/1.01      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.38/1.01      inference(global_propositional_subsumption,
% 3.38/1.01                [status(thm)],
% 3.38/1.01                [c_6421,c_25,c_1812,c_1870,c_2604,c_2866,c_6418]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6466,plain,
% 3.38/1.01      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.38/1.01      inference(renaming,[status(thm)],[c_6465]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_17,negated_conjecture,
% 3.38/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
% 3.38/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1639,plain,
% 3.38/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1651,plain,
% 3.38/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.38/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2245,plain,
% 3.38/1.01      ( r1_tarski(sK7,sK3) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_1639,c_1651]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_6474,plain,
% 3.38/1.01      ( sK2 = k1_xboole_0
% 3.38/1.01      | sK1 = k1_xboole_0
% 3.38/1.01      | r1_tarski(sK7,k1_xboole_0) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_6466,c_2245]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1649,plain,
% 3.38/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.38/1.01      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_3629,plain,
% 3.38/1.01      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_3046,c_1649]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_3938,plain,
% 3.38/1.01      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),X0) = iProver_top
% 3.38/1.01      | r1_tarski(sK7,X0) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_3629,c_1654]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_10731,plain,
% 3.38/1.01      ( r1_tarski(X0,k2_mcart_1(k1_mcart_1(sK9))) != iProver_top
% 3.38/1.01      | r1_tarski(sK7,X0) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_3938,c_1650]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_16810,plain,
% 3.38/1.01      ( r1_tarski(sK7,k1_xboole_0) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_1653,c_10731]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_17231,plain,
% 3.38/1.01      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_6474,c_16810]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_18,negated_conjecture,
% 3.38/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
% 3.38/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1638,plain,
% 3.38/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2246,plain,
% 3.38/1.01      ( r1_tarski(sK6,sK2) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_1638,c_1651]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_17240,plain,
% 3.38/1.01      ( sK1 = k1_xboole_0 | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_17231,c_2246]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_3954,plain,
% 3.38/1.01      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_3630,c_1649]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_4239,plain,
% 3.38/1.01      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),X0) = iProver_top
% 3.38/1.01      | r1_tarski(sK6,X0) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_3954,c_1654]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_16115,plain,
% 3.38/1.01      ( r1_tarski(X0,k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))) != iProver_top
% 3.38/1.01      | r1_tarski(sK6,X0) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_4239,c_1650]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_18110,plain,
% 3.38/1.01      ( r1_tarski(sK6,k1_xboole_0) != iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_1653,c_16115]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_18117,plain,
% 3.38/1.01      ( sK1 = k1_xboole_0 ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_17240,c_18110]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_19,negated_conjecture,
% 3.38/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
% 3.38/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_1637,plain,
% 3.38/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.38/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_2247,plain,
% 3.38/1.01      ( r1_tarski(sK5,sK1) = iProver_top ),
% 3.38/1.01      inference(superposition,[status(thm)],[c_1637,c_1651]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(c_18126,plain,
% 3.38/1.01      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.38/1.01      inference(demodulation,[status(thm)],[c_18117,c_2247]) ).
% 3.38/1.01  
% 3.38/1.01  cnf(contradiction,plain,
% 3.38/1.01      ( $false ),
% 3.38/1.01      inference(minisat,[status(thm)],[c_18292,c_18126]) ).
% 3.38/1.01  
% 3.38/1.01  
% 3.38/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.38/1.01  
% 3.38/1.01  ------                               Statistics
% 3.38/1.01  
% 3.38/1.01  ------ General
% 3.38/1.01  
% 3.38/1.01  abstr_ref_over_cycles:                  0
% 3.38/1.01  abstr_ref_under_cycles:                 0
% 3.38/1.01  gc_basic_clause_elim:                   0
% 3.38/1.01  forced_gc_time:                         0
% 3.38/1.01  parsing_time:                           0.008
% 3.38/1.01  unif_index_cands_time:                  0.
% 3.38/1.01  unif_index_add_time:                    0.
% 3.38/1.01  orderings_time:                         0.
% 3.38/1.01  out_proof_time:                         0.013
% 3.38/1.01  total_time:                             0.467
% 3.38/1.01  num_of_symbols:                         53
% 3.38/1.01  num_of_terms:                           27916
% 3.38/1.01  
% 3.38/1.01  ------ Preprocessing
% 3.38/1.01  
% 3.38/1.01  num_of_splits:                          0
% 3.38/1.01  num_of_split_atoms:                     0
% 3.38/1.01  num_of_reused_defs:                     0
% 3.38/1.01  num_eq_ax_congr_red:                    6
% 3.38/1.01  num_of_sem_filtered_clauses:            1
% 3.38/1.01  num_of_subtypes:                        0
% 3.38/1.01  monotx_restored_types:                  0
% 3.38/1.01  sat_num_of_epr_types:                   0
% 3.38/1.01  sat_num_of_non_cyclic_types:            0
% 3.38/1.01  sat_guarded_non_collapsed_types:        0
% 3.38/1.01  num_pure_diseq_elim:                    0
% 3.38/1.01  simp_replaced_by:                       0
% 3.38/1.01  res_preprocessed:                       87
% 3.38/1.01  prep_upred:                             0
% 3.38/1.01  prep_unflattend:                        47
% 3.38/1.01  smt_new_axioms:                         0
% 3.38/1.01  pred_elim_cands:                        3
% 3.38/1.01  pred_elim:                              0
% 3.38/1.01  pred_elim_cl:                           0
% 3.38/1.01  pred_elim_cycles:                       2
% 3.38/1.01  merged_defs:                            6
% 3.38/1.01  merged_defs_ncl:                        0
% 3.38/1.01  bin_hyper_res:                          6
% 3.38/1.01  prep_cycles:                            3
% 3.38/1.01  pred_elim_time:                         0.01
% 3.38/1.01  splitting_time:                         0.
% 3.38/1.01  sem_filter_time:                        0.
% 3.38/1.01  monotx_time:                            0.
% 3.38/1.01  subtype_inf_time:                       0.
% 3.38/1.01  
% 3.38/1.01  ------ Problem properties
% 3.38/1.01  
% 3.38/1.01  clauses:                                20
% 3.38/1.01  conjectures:                            7
% 3.38/1.01  epr:                                    3
% 3.38/1.01  horn:                                   15
% 3.38/1.01  ground:                                 7
% 3.38/1.01  unary:                                  7
% 3.38/1.01  binary:                                 7
% 3.38/1.01  lits:                                   52
% 3.38/1.01  lits_eq:                                20
% 3.38/1.01  fd_pure:                                0
% 3.38/1.01  fd_pseudo:                              0
% 3.38/1.01  fd_cond:                                4
% 3.38/1.01  fd_pseudo_cond:                         0
% 3.38/1.01  ac_symbols:                             0
% 3.38/1.01  
% 3.38/1.01  ------ Propositional Solver
% 3.38/1.01  
% 3.38/1.01  prop_solver_calls:                      25
% 3.38/1.01  prop_fast_solver_calls:                 991
% 3.38/1.01  smt_solver_calls:                       0
% 3.38/1.01  smt_fast_solver_calls:                  0
% 3.38/1.01  prop_num_of_clauses:                    6803
% 3.38/1.01  prop_preprocess_simplified:             17934
% 3.38/1.01  prop_fo_subsumed:                       9
% 3.38/1.01  prop_solver_time:                       0.
% 3.38/1.01  smt_solver_time:                        0.
% 3.38/1.01  smt_fast_solver_time:                   0.
% 3.38/1.01  prop_fast_solver_time:                  0.
% 3.38/1.01  prop_unsat_core_time:                   0.
% 3.38/1.01  
% 3.38/1.01  ------ QBF
% 3.38/1.01  
% 3.38/1.01  qbf_q_res:                              0
% 3.38/1.01  qbf_num_tautologies:                    0
% 3.38/1.01  qbf_prep_cycles:                        0
% 3.38/1.01  
% 3.38/1.01  ------ BMC1
% 3.38/1.01  
% 3.38/1.01  bmc1_current_bound:                     -1
% 3.38/1.01  bmc1_last_solved_bound:                 -1
% 3.38/1.01  bmc1_unsat_core_size:                   -1
% 3.38/1.01  bmc1_unsat_core_parents_size:           -1
% 3.38/1.01  bmc1_merge_next_fun:                    0
% 3.38/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.38/1.01  
% 3.38/1.01  ------ Instantiation
% 3.38/1.01  
% 3.38/1.01  inst_num_of_clauses:                    2295
% 3.38/1.01  inst_num_in_passive:                    722
% 3.38/1.01  inst_num_in_active:                     513
% 3.38/1.01  inst_num_in_unprocessed:                1060
% 3.38/1.01  inst_num_of_loops:                      540
% 3.38/1.01  inst_num_of_learning_restarts:          0
% 3.38/1.01  inst_num_moves_active_passive:          26
% 3.38/1.01  inst_lit_activity:                      0
% 3.38/1.01  inst_lit_activity_moves:                0
% 3.38/1.01  inst_num_tautologies:                   0
% 3.38/1.01  inst_num_prop_implied:                  0
% 3.38/1.01  inst_num_existing_simplified:           0
% 3.38/1.01  inst_num_eq_res_simplified:             0
% 3.38/1.01  inst_num_child_elim:                    0
% 3.38/1.01  inst_num_of_dismatching_blockings:      122
% 3.38/1.01  inst_num_of_non_proper_insts:           1735
% 3.38/1.01  inst_num_of_duplicates:                 0
% 3.38/1.01  inst_inst_num_from_inst_to_res:         0
% 3.38/1.01  inst_dismatching_checking_time:         0.
% 3.38/1.01  
% 3.38/1.01  ------ Resolution
% 3.38/1.01  
% 3.38/1.01  res_num_of_clauses:                     0
% 3.38/1.01  res_num_in_passive:                     0
% 3.38/1.01  res_num_in_active:                      0
% 3.38/1.01  res_num_of_loops:                       90
% 3.38/1.01  res_forward_subset_subsumed:            25
% 3.38/1.01  res_backward_subset_subsumed:           2
% 3.38/1.01  res_forward_subsumed:                   0
% 3.38/1.01  res_backward_subsumed:                  1
% 3.38/1.01  res_forward_subsumption_resolution:     0
% 3.38/1.01  res_backward_subsumption_resolution:    0
% 3.38/1.01  res_clause_to_clause_subsumption:       526
% 3.38/1.01  res_orphan_elimination:                 0
% 3.38/1.01  res_tautology_del:                      66
% 3.38/1.01  res_num_eq_res_simplified:              0
% 3.38/1.01  res_num_sel_changes:                    0
% 3.38/1.01  res_moves_from_active_to_pass:          0
% 3.38/1.01  
% 3.38/1.01  ------ Superposition
% 3.38/1.01  
% 3.38/1.01  sup_time_total:                         0.
% 3.38/1.01  sup_time_generating:                    0.
% 3.38/1.01  sup_time_sim_full:                      0.
% 3.38/1.01  sup_time_sim_immed:                     0.
% 3.38/1.01  
% 3.38/1.01  sup_num_of_clauses:                     122
% 3.38/1.01  sup_num_in_active:                      79
% 3.38/1.01  sup_num_in_passive:                     43
% 3.38/1.01  sup_num_of_loops:                       107
% 3.38/1.01  sup_fw_superposition:                   78
% 3.38/1.01  sup_bw_superposition:                   125
% 3.38/1.01  sup_immediate_simplified:               43
% 3.38/1.01  sup_given_eliminated:                   0
% 3.38/1.01  comparisons_done:                       0
% 3.38/1.01  comparisons_avoided:                    60
% 3.38/1.01  
% 3.38/1.01  ------ Simplifications
% 3.38/1.01  
% 3.38/1.01  
% 3.38/1.01  sim_fw_subset_subsumed:                 43
% 3.38/1.01  sim_bw_subset_subsumed:                 25
% 3.38/1.01  sim_fw_subsumed:                        0
% 3.38/1.01  sim_bw_subsumed:                        0
% 3.38/1.01  sim_fw_subsumption_res:                 0
% 3.38/1.01  sim_bw_subsumption_res:                 0
% 3.38/1.01  sim_tautology_del:                      1
% 3.38/1.01  sim_eq_tautology_del:                   16
% 3.38/1.01  sim_eq_res_simp:                        0
% 3.38/1.01  sim_fw_demodulated:                     0
% 3.38/1.01  sim_bw_demodulated:                     11
% 3.38/1.01  sim_light_normalised:                   0
% 3.38/1.01  sim_joinable_taut:                      0
% 3.38/1.01  sim_joinable_simp:                      0
% 3.38/1.01  sim_ac_normalised:                      0
% 3.38/1.01  sim_smt_subsumption:                    0
% 3.38/1.01  
%------------------------------------------------------------------------------
