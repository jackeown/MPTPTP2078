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
% DateTime   : Thu Dec  3 11:59:31 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1848)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ? [X8] :
          ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
            | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
            | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
            | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
          & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
          & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
     => ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,sK8),X7)
          | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,sK8),X6)
          | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,sK8),X5)
          | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,sK8),X4) )
        & r2_hidden(sK8,k4_zfmisc_1(X4,X5,X6,X7))
        & m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
            ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),sK7)
              | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
              | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
              | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
            & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,sK7))
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & m1_subset_1(sK7,k1_zfmisc_1(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
                  | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),sK6)
                  | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                  | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                & r2_hidden(X8,k4_zfmisc_1(X4,X5,sK6,X7))
                & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
            & m1_subset_1(X7,k1_zfmisc_1(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
                      | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),sK5)
                      | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                    & r2_hidden(X8,k4_zfmisc_1(X4,sK5,X6,X7))
                    & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                & m1_subset_1(X7,k1_zfmisc_1(X3)) )
            & m1_subset_1(X6,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK5,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
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
                      ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                      & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
              & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
    & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & m1_subset_1(sK7,k1_zfmisc_1(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f13,f18,f17,f16,f15,f14])).

fof(f35,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f42,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f6,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f37])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f37])).

fof(f36,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1729,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1735,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2271,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1735])).

cnf(c_3322,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_1735])).

cnf(c_4418,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3322,c_1735])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1736,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4417,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3322,c_1736])).

cnf(c_3321,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_1736])).

cnf(c_2376,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1736])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1728,plain,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1734,plain,
    ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2385,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1728,c_1734])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1733,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2817,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1728,c_1733])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1732,plain,
    ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4432,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1728,c_1732])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1731,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2267,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1728,c_1731])).

cnf(c_8,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1730,plain,
    ( r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) != iProver_top
    | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3779,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2267,c_1730])).

cnf(c_20,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1854,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1855,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
    | r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1854])).

cnf(c_1901,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1905,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1901])).

cnf(c_2055,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2059,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) = iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2055])).

cnf(c_4045,plain,
    ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
    | sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3779,c_20,c_1855,c_1905,c_2059])).

cnf(c_4046,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4045])).

cnf(c_5104,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4432,c_4046])).

cnf(c_2056,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2057,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2056])).

cnf(c_5107,plain,
    ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5104,c_20,c_1855,c_1905,c_2057])).

cnf(c_5108,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5107])).

cnf(c_5117,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2817,c_5108])).

cnf(c_1902,plain,
    ( ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1903,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1902])).

cnf(c_6098,plain,
    ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5117,c_20,c_1855,c_1903])).

cnf(c_6099,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_6098])).

cnf(c_6107,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK8),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2385,c_6099])).

cnf(c_1847,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7)
    | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6108,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6107])).

cnf(c_6110,plain,
    ( sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6107,c_20,c_1848])).

cnf(c_6111,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6110])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1727,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6122,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6111,c_1727])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_165,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_166,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_165])).

cnf(c_1723,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166])).

cnf(c_6971,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6122,c_1723])).

cnf(c_8167,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2376,c_6971])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1726,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8833,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8167,c_1726])).

cnf(c_8865,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8833,c_1723])).

cnf(c_9076,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3321,c_8865])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1725,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9085,plain,
    ( sK0 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9076,c_1725])).

cnf(c_9131,plain,
    ( sK0 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9085,c_1723])).

cnf(c_9147,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4417,c_9131])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1724,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9329,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9147,c_1724])).

cnf(c_9347,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9329,c_1723])).

cnf(c_10258,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4418,c_9347])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.15/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/0.97  
% 2.15/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.15/0.97  
% 2.15/0.97  ------  iProver source info
% 2.15/0.97  
% 2.15/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.15/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.15/0.97  git: non_committed_changes: false
% 2.15/0.97  git: last_make_outside_of_git: false
% 2.15/0.97  
% 2.15/0.97  ------ 
% 2.15/0.97  
% 2.15/0.97  ------ Input Options
% 2.15/0.97  
% 2.15/0.97  --out_options                           all
% 2.15/0.97  --tptp_safe_out                         true
% 2.15/0.97  --problem_path                          ""
% 2.15/0.97  --include_path                          ""
% 2.15/0.97  --clausifier                            res/vclausify_rel
% 2.15/0.97  --clausifier_options                    --mode clausify
% 2.15/0.97  --stdin                                 false
% 2.15/0.97  --stats_out                             all
% 2.15/0.97  
% 2.15/0.97  ------ General Options
% 2.15/0.97  
% 2.15/0.97  --fof                                   false
% 2.15/0.97  --time_out_real                         305.
% 2.15/0.97  --time_out_virtual                      -1.
% 2.15/0.97  --symbol_type_check                     false
% 2.15/0.97  --clausify_out                          false
% 2.15/0.97  --sig_cnt_out                           false
% 2.15/0.97  --trig_cnt_out                          false
% 2.15/0.97  --trig_cnt_out_tolerance                1.
% 2.15/0.97  --trig_cnt_out_sk_spl                   false
% 2.15/0.97  --abstr_cl_out                          false
% 2.15/0.97  
% 2.15/0.97  ------ Global Options
% 2.15/0.97  
% 2.15/0.97  --schedule                              default
% 2.15/0.97  --add_important_lit                     false
% 2.15/0.97  --prop_solver_per_cl                    1000
% 2.15/0.97  --min_unsat_core                        false
% 2.15/0.97  --soft_assumptions                      false
% 2.15/0.97  --soft_lemma_size                       3
% 2.15/0.97  --prop_impl_unit_size                   0
% 2.15/0.97  --prop_impl_unit                        []
% 2.15/0.97  --share_sel_clauses                     true
% 2.15/0.97  --reset_solvers                         false
% 2.15/0.97  --bc_imp_inh                            [conj_cone]
% 2.15/0.97  --conj_cone_tolerance                   3.
% 2.15/0.97  --extra_neg_conj                        none
% 2.15/0.97  --large_theory_mode                     true
% 2.15/0.97  --prolific_symb_bound                   200
% 2.15/0.97  --lt_threshold                          2000
% 2.15/0.97  --clause_weak_htbl                      true
% 2.15/0.97  --gc_record_bc_elim                     false
% 2.15/0.97  
% 2.15/0.97  ------ Preprocessing Options
% 2.15/0.97  
% 2.15/0.97  --preprocessing_flag                    true
% 2.15/0.97  --time_out_prep_mult                    0.1
% 2.15/0.97  --splitting_mode                        input
% 2.15/0.97  --splitting_grd                         true
% 2.15/0.97  --splitting_cvd                         false
% 2.15/0.97  --splitting_cvd_svl                     false
% 2.15/0.97  --splitting_nvd                         32
% 2.15/0.97  --sub_typing                            true
% 2.15/0.97  --prep_gs_sim                           true
% 2.15/0.97  --prep_unflatten                        true
% 2.15/0.97  --prep_res_sim                          true
% 2.15/0.97  --prep_upred                            true
% 2.15/0.97  --prep_sem_filter                       exhaustive
% 2.15/0.97  --prep_sem_filter_out                   false
% 2.15/0.97  --pred_elim                             true
% 2.15/0.97  --res_sim_input                         true
% 2.15/0.97  --eq_ax_congr_red                       true
% 2.15/0.97  --pure_diseq_elim                       true
% 2.15/0.97  --brand_transform                       false
% 2.15/0.97  --non_eq_to_eq                          false
% 2.15/0.97  --prep_def_merge                        true
% 2.15/0.97  --prep_def_merge_prop_impl              false
% 2.15/0.97  --prep_def_merge_mbd                    true
% 2.15/0.97  --prep_def_merge_tr_red                 false
% 2.15/0.97  --prep_def_merge_tr_cl                  false
% 2.15/0.97  --smt_preprocessing                     true
% 2.15/0.97  --smt_ac_axioms                         fast
% 2.15/0.97  --preprocessed_out                      false
% 2.15/0.97  --preprocessed_stats                    false
% 2.15/0.97  
% 2.15/0.97  ------ Abstraction refinement Options
% 2.15/0.97  
% 2.15/0.97  --abstr_ref                             []
% 2.15/0.97  --abstr_ref_prep                        false
% 2.15/0.97  --abstr_ref_until_sat                   false
% 2.15/0.97  --abstr_ref_sig_restrict                funpre
% 2.15/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/0.97  --abstr_ref_under                       []
% 2.15/0.97  
% 2.15/0.97  ------ SAT Options
% 2.15/0.97  
% 2.15/0.97  --sat_mode                              false
% 2.15/0.97  --sat_fm_restart_options                ""
% 2.15/0.97  --sat_gr_def                            false
% 2.15/0.97  --sat_epr_types                         true
% 2.15/0.97  --sat_non_cyclic_types                  false
% 2.15/0.97  --sat_finite_models                     false
% 2.15/0.97  --sat_fm_lemmas                         false
% 2.15/0.97  --sat_fm_prep                           false
% 2.15/0.97  --sat_fm_uc_incr                        true
% 2.15/0.97  --sat_out_model                         small
% 2.15/0.97  --sat_out_clauses                       false
% 2.15/0.97  
% 2.15/0.97  ------ QBF Options
% 2.15/0.97  
% 2.15/0.97  --qbf_mode                              false
% 2.15/0.97  --qbf_elim_univ                         false
% 2.15/0.97  --qbf_dom_inst                          none
% 2.15/0.97  --qbf_dom_pre_inst                      false
% 2.15/0.97  --qbf_sk_in                             false
% 2.15/0.97  --qbf_pred_elim                         true
% 2.15/0.97  --qbf_split                             512
% 2.15/0.97  
% 2.15/0.97  ------ BMC1 Options
% 2.15/0.97  
% 2.15/0.97  --bmc1_incremental                      false
% 2.15/0.97  --bmc1_axioms                           reachable_all
% 2.15/0.97  --bmc1_min_bound                        0
% 2.15/0.97  --bmc1_max_bound                        -1
% 2.15/0.97  --bmc1_max_bound_default                -1
% 2.15/0.97  --bmc1_symbol_reachability              true
% 2.15/0.97  --bmc1_property_lemmas                  false
% 2.15/0.97  --bmc1_k_induction                      false
% 2.15/0.97  --bmc1_non_equiv_states                 false
% 2.15/0.97  --bmc1_deadlock                         false
% 2.15/0.97  --bmc1_ucm                              false
% 2.15/0.97  --bmc1_add_unsat_core                   none
% 2.15/0.97  --bmc1_unsat_core_children              false
% 2.15/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/0.97  --bmc1_out_stat                         full
% 2.15/0.97  --bmc1_ground_init                      false
% 2.15/0.97  --bmc1_pre_inst_next_state              false
% 2.15/0.97  --bmc1_pre_inst_state                   false
% 2.15/0.97  --bmc1_pre_inst_reach_state             false
% 2.15/0.97  --bmc1_out_unsat_core                   false
% 2.15/0.97  --bmc1_aig_witness_out                  false
% 2.15/0.97  --bmc1_verbose                          false
% 2.15/0.97  --bmc1_dump_clauses_tptp                false
% 2.15/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.15/0.97  --bmc1_dump_file                        -
% 2.15/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.15/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.15/0.97  --bmc1_ucm_extend_mode                  1
% 2.15/0.97  --bmc1_ucm_init_mode                    2
% 2.15/0.97  --bmc1_ucm_cone_mode                    none
% 2.15/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.15/0.97  --bmc1_ucm_relax_model                  4
% 2.15/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.15/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/0.97  --bmc1_ucm_layered_model                none
% 2.15/0.97  --bmc1_ucm_max_lemma_size               10
% 2.15/0.97  
% 2.15/0.97  ------ AIG Options
% 2.15/0.97  
% 2.15/0.97  --aig_mode                              false
% 2.15/0.97  
% 2.15/0.97  ------ Instantiation Options
% 2.15/0.97  
% 2.15/0.97  --instantiation_flag                    true
% 2.15/0.97  --inst_sos_flag                         false
% 2.15/0.97  --inst_sos_phase                        true
% 2.15/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/0.97  --inst_lit_sel_side                     num_symb
% 2.15/0.97  --inst_solver_per_active                1400
% 2.15/0.97  --inst_solver_calls_frac                1.
% 2.15/0.97  --inst_passive_queue_type               priority_queues
% 2.15/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/0.97  --inst_passive_queues_freq              [25;2]
% 2.15/0.97  --inst_dismatching                      true
% 2.15/0.97  --inst_eager_unprocessed_to_passive     true
% 2.15/0.97  --inst_prop_sim_given                   true
% 2.15/0.97  --inst_prop_sim_new                     false
% 2.15/0.97  --inst_subs_new                         false
% 2.15/0.97  --inst_eq_res_simp                      false
% 2.15/0.97  --inst_subs_given                       false
% 2.15/0.97  --inst_orphan_elimination               true
% 2.15/0.97  --inst_learning_loop_flag               true
% 2.15/0.97  --inst_learning_start                   3000
% 2.15/0.97  --inst_learning_factor                  2
% 2.15/0.97  --inst_start_prop_sim_after_learn       3
% 2.15/0.97  --inst_sel_renew                        solver
% 2.15/0.97  --inst_lit_activity_flag                true
% 2.15/0.97  --inst_restr_to_given                   false
% 2.15/0.97  --inst_activity_threshold               500
% 2.15/0.97  --inst_out_proof                        true
% 2.15/0.97  
% 2.15/0.97  ------ Resolution Options
% 2.15/0.97  
% 2.15/0.97  --resolution_flag                       true
% 2.15/0.97  --res_lit_sel                           adaptive
% 2.15/0.97  --res_lit_sel_side                      none
% 2.15/0.97  --res_ordering                          kbo
% 2.15/0.97  --res_to_prop_solver                    active
% 2.15/0.97  --res_prop_simpl_new                    false
% 2.15/0.97  --res_prop_simpl_given                  true
% 2.15/0.97  --res_passive_queue_type                priority_queues
% 2.15/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/0.97  --res_passive_queues_freq               [15;5]
% 2.15/0.97  --res_forward_subs                      full
% 2.15/0.97  --res_backward_subs                     full
% 2.15/0.97  --res_forward_subs_resolution           true
% 2.15/0.97  --res_backward_subs_resolution          true
% 2.15/0.97  --res_orphan_elimination                true
% 2.15/0.97  --res_time_limit                        2.
% 2.15/0.97  --res_out_proof                         true
% 2.15/0.97  
% 2.15/0.97  ------ Superposition Options
% 2.15/0.97  
% 2.15/0.97  --superposition_flag                    true
% 2.15/0.97  --sup_passive_queue_type                priority_queues
% 2.15/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.15/0.97  --demod_completeness_check              fast
% 2.15/0.97  --demod_use_ground                      true
% 2.15/0.97  --sup_to_prop_solver                    passive
% 2.15/0.97  --sup_prop_simpl_new                    true
% 2.15/0.97  --sup_prop_simpl_given                  true
% 2.15/0.97  --sup_fun_splitting                     false
% 2.15/0.97  --sup_smt_interval                      50000
% 2.15/0.97  
% 2.15/0.97  ------ Superposition Simplification Setup
% 2.15/0.97  
% 2.15/0.97  --sup_indices_passive                   []
% 2.15/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.97  --sup_full_bw                           [BwDemod]
% 2.15/0.97  --sup_immed_triv                        [TrivRules]
% 2.15/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.97  --sup_immed_bw_main                     []
% 2.15/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/0.97  
% 2.15/0.97  ------ Combination Options
% 2.15/0.97  
% 2.15/0.97  --comb_res_mult                         3
% 2.15/0.97  --comb_sup_mult                         2
% 2.15/0.97  --comb_inst_mult                        10
% 2.15/0.97  
% 2.15/0.97  ------ Debug Options
% 2.15/0.97  
% 2.15/0.97  --dbg_backtrace                         false
% 2.15/0.97  --dbg_dump_prop_clauses                 false
% 2.15/0.97  --dbg_dump_prop_clauses_file            -
% 2.15/0.97  --dbg_out_stat                          false
% 2.15/0.97  ------ Parsing...
% 2.15/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.15/0.97  
% 2.15/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.15/0.97  
% 2.15/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.15/0.97  
% 2.15/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.15/0.97  ------ Proving...
% 2.15/0.97  ------ Problem Properties 
% 2.15/0.97  
% 2.15/0.97  
% 2.15/0.97  clauses                                 14
% 2.15/0.97  conjectures                             7
% 2.15/0.97  EPR                                     0
% 2.15/0.97  Horn                                    10
% 2.15/0.97  unary                                   6
% 2.15/0.97  binary                                  3
% 2.15/0.97  lits                                    40
% 2.15/0.97  lits eq                                 20
% 2.15/0.97  fd_pure                                 0
% 2.15/0.97  fd_pseudo                               0
% 2.15/0.97  fd_cond                                 4
% 2.15/0.97  fd_pseudo_cond                          0
% 2.15/0.97  AC symbols                              0
% 2.15/0.97  
% 2.15/0.97  ------ Schedule dynamic 5 is on 
% 2.15/0.97  
% 2.15/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.15/0.97  
% 2.15/0.97  
% 2.15/0.97  ------ 
% 2.15/0.97  Current options:
% 2.15/0.97  ------ 
% 2.15/0.97  
% 2.15/0.97  ------ Input Options
% 2.15/0.97  
% 2.15/0.97  --out_options                           all
% 2.15/0.97  --tptp_safe_out                         true
% 2.15/0.97  --problem_path                          ""
% 2.15/0.97  --include_path                          ""
% 2.15/0.97  --clausifier                            res/vclausify_rel
% 2.15/0.97  --clausifier_options                    --mode clausify
% 2.15/0.97  --stdin                                 false
% 2.15/0.97  --stats_out                             all
% 2.15/0.97  
% 2.15/0.97  ------ General Options
% 2.15/0.97  
% 2.15/0.97  --fof                                   false
% 2.15/0.97  --time_out_real                         305.
% 2.15/0.97  --time_out_virtual                      -1.
% 2.15/0.97  --symbol_type_check                     false
% 2.15/0.97  --clausify_out                          false
% 2.15/0.97  --sig_cnt_out                           false
% 2.15/0.97  --trig_cnt_out                          false
% 2.15/0.97  --trig_cnt_out_tolerance                1.
% 2.15/0.97  --trig_cnt_out_sk_spl                   false
% 2.15/0.97  --abstr_cl_out                          false
% 2.15/0.97  
% 2.15/0.97  ------ Global Options
% 2.15/0.97  
% 2.15/0.97  --schedule                              default
% 2.15/0.97  --add_important_lit                     false
% 2.15/0.97  --prop_solver_per_cl                    1000
% 2.15/0.97  --min_unsat_core                        false
% 2.15/0.97  --soft_assumptions                      false
% 2.15/0.97  --soft_lemma_size                       3
% 2.15/0.97  --prop_impl_unit_size                   0
% 2.15/0.97  --prop_impl_unit                        []
% 2.15/0.97  --share_sel_clauses                     true
% 2.15/0.97  --reset_solvers                         false
% 2.15/0.97  --bc_imp_inh                            [conj_cone]
% 2.15/0.97  --conj_cone_tolerance                   3.
% 2.15/0.97  --extra_neg_conj                        none
% 2.15/0.97  --large_theory_mode                     true
% 2.15/0.97  --prolific_symb_bound                   200
% 2.15/0.97  --lt_threshold                          2000
% 2.15/0.97  --clause_weak_htbl                      true
% 2.15/0.97  --gc_record_bc_elim                     false
% 2.15/0.97  
% 2.15/0.97  ------ Preprocessing Options
% 2.15/0.97  
% 2.15/0.97  --preprocessing_flag                    true
% 2.15/0.97  --time_out_prep_mult                    0.1
% 2.15/0.97  --splitting_mode                        input
% 2.15/0.97  --splitting_grd                         true
% 2.15/0.97  --splitting_cvd                         false
% 2.15/0.97  --splitting_cvd_svl                     false
% 2.15/0.97  --splitting_nvd                         32
% 2.15/0.97  --sub_typing                            true
% 2.15/0.97  --prep_gs_sim                           true
% 2.15/0.97  --prep_unflatten                        true
% 2.15/0.97  --prep_res_sim                          true
% 2.15/0.97  --prep_upred                            true
% 2.15/0.97  --prep_sem_filter                       exhaustive
% 2.15/0.97  --prep_sem_filter_out                   false
% 2.15/0.97  --pred_elim                             true
% 2.15/0.97  --res_sim_input                         true
% 2.15/0.97  --eq_ax_congr_red                       true
% 2.15/0.97  --pure_diseq_elim                       true
% 2.15/0.97  --brand_transform                       false
% 2.15/0.97  --non_eq_to_eq                          false
% 2.15/0.97  --prep_def_merge                        true
% 2.15/0.97  --prep_def_merge_prop_impl              false
% 2.15/0.97  --prep_def_merge_mbd                    true
% 2.15/0.97  --prep_def_merge_tr_red                 false
% 2.15/0.97  --prep_def_merge_tr_cl                  false
% 2.15/0.97  --smt_preprocessing                     true
% 2.15/0.97  --smt_ac_axioms                         fast
% 2.15/0.97  --preprocessed_out                      false
% 2.15/0.97  --preprocessed_stats                    false
% 2.15/0.97  
% 2.15/0.97  ------ Abstraction refinement Options
% 2.15/0.97  
% 2.15/0.97  --abstr_ref                             []
% 2.15/0.97  --abstr_ref_prep                        false
% 2.15/0.97  --abstr_ref_until_sat                   false
% 2.15/0.97  --abstr_ref_sig_restrict                funpre
% 2.15/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/0.97  --abstr_ref_under                       []
% 2.15/0.97  
% 2.15/0.97  ------ SAT Options
% 2.15/0.97  
% 2.15/0.97  --sat_mode                              false
% 2.15/0.97  --sat_fm_restart_options                ""
% 2.15/0.97  --sat_gr_def                            false
% 2.15/0.97  --sat_epr_types                         true
% 2.15/0.97  --sat_non_cyclic_types                  false
% 2.15/0.97  --sat_finite_models                     false
% 2.15/0.97  --sat_fm_lemmas                         false
% 2.15/0.97  --sat_fm_prep                           false
% 2.15/0.97  --sat_fm_uc_incr                        true
% 2.15/0.97  --sat_out_model                         small
% 2.15/0.97  --sat_out_clauses                       false
% 2.15/0.97  
% 2.15/0.97  ------ QBF Options
% 2.15/0.97  
% 2.15/0.97  --qbf_mode                              false
% 2.15/0.97  --qbf_elim_univ                         false
% 2.15/0.97  --qbf_dom_inst                          none
% 2.15/0.97  --qbf_dom_pre_inst                      false
% 2.15/0.97  --qbf_sk_in                             false
% 2.15/0.97  --qbf_pred_elim                         true
% 2.15/0.97  --qbf_split                             512
% 2.15/0.97  
% 2.15/0.97  ------ BMC1 Options
% 2.15/0.97  
% 2.15/0.97  --bmc1_incremental                      false
% 2.15/0.97  --bmc1_axioms                           reachable_all
% 2.15/0.97  --bmc1_min_bound                        0
% 2.15/0.97  --bmc1_max_bound                        -1
% 2.15/0.97  --bmc1_max_bound_default                -1
% 2.15/0.97  --bmc1_symbol_reachability              true
% 2.15/0.97  --bmc1_property_lemmas                  false
% 2.15/0.97  --bmc1_k_induction                      false
% 2.15/0.97  --bmc1_non_equiv_states                 false
% 2.15/0.97  --bmc1_deadlock                         false
% 2.15/0.97  --bmc1_ucm                              false
% 2.15/0.97  --bmc1_add_unsat_core                   none
% 2.15/0.97  --bmc1_unsat_core_children              false
% 2.15/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/0.97  --bmc1_out_stat                         full
% 2.15/0.97  --bmc1_ground_init                      false
% 2.15/0.97  --bmc1_pre_inst_next_state              false
% 2.15/0.97  --bmc1_pre_inst_state                   false
% 2.15/0.97  --bmc1_pre_inst_reach_state             false
% 2.15/0.97  --bmc1_out_unsat_core                   false
% 2.15/0.97  --bmc1_aig_witness_out                  false
% 2.15/0.97  --bmc1_verbose                          false
% 2.15/0.97  --bmc1_dump_clauses_tptp                false
% 2.15/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.15/0.97  --bmc1_dump_file                        -
% 2.15/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.15/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.15/0.97  --bmc1_ucm_extend_mode                  1
% 2.15/0.97  --bmc1_ucm_init_mode                    2
% 2.15/0.97  --bmc1_ucm_cone_mode                    none
% 2.15/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.15/0.97  --bmc1_ucm_relax_model                  4
% 2.15/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.15/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/0.97  --bmc1_ucm_layered_model                none
% 2.15/0.97  --bmc1_ucm_max_lemma_size               10
% 2.15/0.97  
% 2.15/0.97  ------ AIG Options
% 2.15/0.97  
% 2.15/0.97  --aig_mode                              false
% 2.15/0.97  
% 2.15/0.97  ------ Instantiation Options
% 2.15/0.97  
% 2.15/0.97  --instantiation_flag                    true
% 2.15/0.97  --inst_sos_flag                         false
% 2.15/0.97  --inst_sos_phase                        true
% 2.15/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/0.97  --inst_lit_sel_side                     none
% 2.15/0.97  --inst_solver_per_active                1400
% 2.15/0.97  --inst_solver_calls_frac                1.
% 2.15/0.97  --inst_passive_queue_type               priority_queues
% 2.15/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/0.97  --inst_passive_queues_freq              [25;2]
% 2.15/0.97  --inst_dismatching                      true
% 2.15/0.97  --inst_eager_unprocessed_to_passive     true
% 2.15/0.97  --inst_prop_sim_given                   true
% 2.15/0.97  --inst_prop_sim_new                     false
% 2.15/0.97  --inst_subs_new                         false
% 2.15/0.97  --inst_eq_res_simp                      false
% 2.15/0.97  --inst_subs_given                       false
% 2.15/0.97  --inst_orphan_elimination               true
% 2.15/0.97  --inst_learning_loop_flag               true
% 2.15/0.97  --inst_learning_start                   3000
% 2.15/0.97  --inst_learning_factor                  2
% 2.15/0.97  --inst_start_prop_sim_after_learn       3
% 2.15/0.97  --inst_sel_renew                        solver
% 2.15/0.97  --inst_lit_activity_flag                true
% 2.15/0.97  --inst_restr_to_given                   false
% 2.15/0.97  --inst_activity_threshold               500
% 2.15/0.97  --inst_out_proof                        true
% 2.15/0.97  
% 2.15/0.97  ------ Resolution Options
% 2.15/0.97  
% 2.15/0.97  --resolution_flag                       false
% 2.15/0.97  --res_lit_sel                           adaptive
% 2.15/0.97  --res_lit_sel_side                      none
% 2.15/0.97  --res_ordering                          kbo
% 2.15/0.97  --res_to_prop_solver                    active
% 2.15/0.97  --res_prop_simpl_new                    false
% 2.15/0.97  --res_prop_simpl_given                  true
% 2.15/0.97  --res_passive_queue_type                priority_queues
% 2.15/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/0.97  --res_passive_queues_freq               [15;5]
% 2.15/0.97  --res_forward_subs                      full
% 2.15/0.97  --res_backward_subs                     full
% 2.15/0.97  --res_forward_subs_resolution           true
% 2.15/0.97  --res_backward_subs_resolution          true
% 2.15/0.97  --res_orphan_elimination                true
% 2.15/0.97  --res_time_limit                        2.
% 2.15/0.97  --res_out_proof                         true
% 2.15/0.97  
% 2.15/0.97  ------ Superposition Options
% 2.15/0.97  
% 2.15/0.97  --superposition_flag                    true
% 2.15/0.97  --sup_passive_queue_type                priority_queues
% 2.15/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.15/0.97  --demod_completeness_check              fast
% 2.15/0.97  --demod_use_ground                      true
% 2.15/0.97  --sup_to_prop_solver                    passive
% 2.15/0.97  --sup_prop_simpl_new                    true
% 2.15/0.97  --sup_prop_simpl_given                  true
% 2.15/0.97  --sup_fun_splitting                     false
% 2.15/0.97  --sup_smt_interval                      50000
% 2.15/0.97  
% 2.15/0.97  ------ Superposition Simplification Setup
% 2.15/0.97  
% 2.15/0.97  --sup_indices_passive                   []
% 2.15/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.97  --sup_full_bw                           [BwDemod]
% 2.15/0.97  --sup_immed_triv                        [TrivRules]
% 2.15/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.97  --sup_immed_bw_main                     []
% 2.15/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/0.97  
% 2.15/0.97  ------ Combination Options
% 2.15/0.97  
% 2.15/0.97  --comb_res_mult                         3
% 2.15/0.97  --comb_sup_mult                         2
% 2.15/0.97  --comb_inst_mult                        10
% 2.15/0.97  
% 2.15/0.97  ------ Debug Options
% 2.15/0.97  
% 2.15/0.97  --dbg_backtrace                         false
% 2.15/0.97  --dbg_dump_prop_clauses                 false
% 2.15/0.97  --dbg_dump_prop_clauses_file            -
% 2.15/0.97  --dbg_out_stat                          false
% 2.15/0.97  
% 2.15/0.97  
% 2.15/0.97  
% 2.15/0.97  
% 2.15/0.97  ------ Proving...
% 2.15/0.97  
% 2.15/0.97  
% 2.15/0.97  % SZS status Theorem for theBenchmark.p
% 2.15/0.97  
% 2.15/0.97   Resolution empty clause
% 2.15/0.97  
% 2.15/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.15/0.97  
% 2.15/0.97  fof(f7,conjecture,(
% 2.15/0.97    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 2.15/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/0.97  
% 2.15/0.97  fof(f8,negated_conjecture,(
% 2.15/0.97    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 2.15/0.97    inference(negated_conjecture,[],[f7])).
% 2.15/0.97  
% 2.15/0.97  fof(f12,plain,(
% 2.15/0.97    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 2.15/0.97    inference(ennf_transformation,[],[f8])).
% 2.15/0.97  
% 2.15/0.97  fof(f13,plain,(
% 2.15/0.97    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 2.15/0.97    inference(flattening,[],[f12])).
% 2.15/0.97  
% 2.15/0.97  fof(f18,plain,(
% 2.15/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) => ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,sK8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,sK8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,sK8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,sK8),X4)) & r2_hidden(sK8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3)))) )),
% 2.15/0.97    introduced(choice_axiom,[])).
% 2.15/0.97  
% 2.15/0.97  fof(f17,plain,(
% 2.15/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),sK7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(X3)))) )),
% 2.15/0.97    introduced(choice_axiom,[])).
% 2.15/0.97  
% 2.15/0.97  fof(f16,plain,(
% 2.15/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),sK6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(sK6,k1_zfmisc_1(X2)))) )),
% 2.15/0.97    introduced(choice_axiom,[])).
% 2.15/0.97  
% 2.15/0.97  fof(f15,plain,(
% 2.15/0.97    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),sK5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 2.15/0.97    introduced(choice_axiom,[])).
% 2.15/0.97  
% 2.15/0.97  fof(f14,plain,(
% 2.15/0.97    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0)))),
% 2.15/0.97    introduced(choice_axiom,[])).
% 2.15/0.97  
% 2.15/0.97  fof(f19,plain,(
% 2.15/0.97    (((((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 2.15/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f13,f18,f17,f16,f15,f14])).
% 2.15/0.97  
% 2.15/0.97  fof(f35,plain,(
% 2.15/0.97    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.15/0.97    inference(cnf_transformation,[],[f19])).
% 2.15/0.97  
% 2.15/0.97  fof(f4,axiom,(
% 2.15/0.97    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 2.15/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/0.97  
% 2.15/0.97  fof(f23,plain,(
% 2.15/0.97    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.15/0.97    inference(cnf_transformation,[],[f4])).
% 2.15/0.97  
% 2.15/0.97  fof(f3,axiom,(
% 2.15/0.97    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.15/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/0.97  
% 2.15/0.97  fof(f22,plain,(
% 2.15/0.97    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.15/0.97    inference(cnf_transformation,[],[f3])).
% 2.15/0.97  
% 2.15/0.97  fof(f37,plain,(
% 2.15/0.97    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.15/0.97    inference(definition_unfolding,[],[f23,f22])).
% 2.15/0.97  
% 2.15/0.97  fof(f42,plain,(
% 2.15/0.97    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 2.15/0.97    inference(definition_unfolding,[],[f35,f37])).
% 2.15/0.97  
% 2.15/0.97  fof(f5,axiom,(
% 2.15/0.97    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.15/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/0.97  
% 2.15/0.97  fof(f10,plain,(
% 2.15/0.97    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.15/0.97    inference(ennf_transformation,[],[f5])).
% 2.15/0.97  
% 2.15/0.97  fof(f24,plain,(
% 2.15/0.97    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.15/0.97    inference(cnf_transformation,[],[f10])).
% 2.15/0.97  
% 2.15/0.97  fof(f25,plain,(
% 2.15/0.97    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.15/0.97    inference(cnf_transformation,[],[f10])).
% 2.15/0.97  
% 2.15/0.97  fof(f34,plain,(
% 2.15/0.97    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 2.15/0.97    inference(cnf_transformation,[],[f19])).
% 2.15/0.97  
% 2.15/0.97  fof(f43,plain,(
% 2.15/0.97    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 2.15/0.97    inference(definition_unfolding,[],[f34,f37])).
% 2.15/0.97  
% 2.15/0.97  fof(f6,axiom,(
% 2.15/0.97    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.15/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/0.97  
% 2.15/0.97  fof(f11,plain,(
% 2.15/0.97    ! [X0,X1,X2,X3] : (! [X4] : ((k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.15/0.97    inference(ennf_transformation,[],[f6])).
% 2.15/0.97  
% 2.15/0.97  fof(f29,plain,(
% 2.15/0.97    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.15/0.97    inference(cnf_transformation,[],[f11])).
% 2.15/0.97  
% 2.15/0.97  fof(f38,plain,(
% 2.15/0.97    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.15/0.97    inference(definition_unfolding,[],[f29,f37])).
% 2.15/0.97  
% 2.15/0.97  fof(f28,plain,(
% 2.15/0.97    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.15/0.97    inference(cnf_transformation,[],[f11])).
% 2.15/0.97  
% 2.15/0.97  fof(f39,plain,(
% 2.15/0.97    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.15/0.97    inference(definition_unfolding,[],[f28,f37])).
% 2.15/0.97  
% 2.15/0.97  fof(f27,plain,(
% 2.15/0.97    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.15/0.97    inference(cnf_transformation,[],[f11])).
% 2.15/0.97  
% 2.15/0.97  fof(f40,plain,(
% 2.15/0.97    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.15/0.97    inference(definition_unfolding,[],[f27,f37])).
% 2.15/0.97  
% 2.15/0.97  fof(f26,plain,(
% 2.15/0.97    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.15/0.97    inference(cnf_transformation,[],[f11])).
% 2.15/0.97  
% 2.15/0.97  fof(f41,plain,(
% 2.15/0.97    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.15/0.97    inference(definition_unfolding,[],[f26,f37])).
% 2.15/0.97  
% 2.15/0.97  fof(f36,plain,(
% 2.15/0.97    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 2.15/0.97    inference(cnf_transformation,[],[f19])).
% 2.15/0.97  
% 2.15/0.97  fof(f33,plain,(
% 2.15/0.97    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 2.15/0.97    inference(cnf_transformation,[],[f19])).
% 2.15/0.97  
% 2.15/0.97  fof(f1,axiom,(
% 2.15/0.97    v1_xboole_0(k1_xboole_0)),
% 2.15/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/0.97  
% 2.15/0.97  fof(f20,plain,(
% 2.15/0.97    v1_xboole_0(k1_xboole_0)),
% 2.15/0.97    inference(cnf_transformation,[],[f1])).
% 2.15/0.97  
% 2.15/0.97  fof(f2,axiom,(
% 2.15/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.15/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/0.97  
% 2.15/0.97  fof(f9,plain,(
% 2.15/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.15/0.97    inference(ennf_transformation,[],[f2])).
% 2.15/0.97  
% 2.15/0.97  fof(f21,plain,(
% 2.15/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.15/0.97    inference(cnf_transformation,[],[f9])).
% 2.15/0.97  
% 2.15/0.97  fof(f32,plain,(
% 2.15/0.97    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 2.15/0.97    inference(cnf_transformation,[],[f19])).
% 2.15/0.97  
% 2.15/0.97  fof(f31,plain,(
% 2.15/0.97    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 2.15/0.97    inference(cnf_transformation,[],[f19])).
% 2.15/0.97  
% 2.15/0.97  fof(f30,plain,(
% 2.15/0.97    m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 2.15/0.97    inference(cnf_transformation,[],[f19])).
% 2.15/0.97  
% 2.15/0.97  cnf(c_9,negated_conjecture,
% 2.15/0.97      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
% 2.15/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1729,plain,
% 2.15/0.97      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_3,plain,
% 2.15/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.15/0.97      inference(cnf_transformation,[],[f24]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1735,plain,
% 2.15/0.97      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.15/0.97      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_2271,plain,
% 2.15/0.97      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_1729,c_1735]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_3322,plain,
% 2.15/0.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_2271,c_1735]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_4418,plain,
% 2.15/0.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) = iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_3322,c_1735]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_2,plain,
% 2.15/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.15/0.97      inference(cnf_transformation,[],[f25]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1736,plain,
% 2.15/0.97      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.15/0.97      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_4417,plain,
% 2.15/0.97      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) = iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_3322,c_1736]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_3321,plain,
% 2.15/0.97      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_2271,c_1736]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_2376,plain,
% 2.15/0.97      ( r2_hidden(k2_mcart_1(sK8),sK7) = iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_1729,c_1736]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_10,negated_conjecture,
% 2.15/0.97      ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
% 2.15/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1728,plain,
% 2.15/0.97      ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) = iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_4,plain,
% 2.15/0.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.15/0.97      | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
% 2.15/0.97      | k1_xboole_0 = X4
% 2.15/0.97      | k1_xboole_0 = X3
% 2.15/0.97      | k1_xboole_0 = X2
% 2.15/0.97      | k1_xboole_0 = X1 ),
% 2.15/0.97      inference(cnf_transformation,[],[f38]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1734,plain,
% 2.15/0.97      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
% 2.15/0.97      | k1_xboole_0 = X3
% 2.15/0.97      | k1_xboole_0 = X0
% 2.15/0.97      | k1_xboole_0 = X1
% 2.15/0.97      | k1_xboole_0 = X2
% 2.15/0.97      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_2385,plain,
% 2.15/0.97      ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
% 2.15/0.97      | sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0 ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_1728,c_1734]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_5,plain,
% 2.15/0.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.15/0.97      | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.15/0.97      | k1_xboole_0 = X4
% 2.15/0.97      | k1_xboole_0 = X3
% 2.15/0.97      | k1_xboole_0 = X2
% 2.15/0.97      | k1_xboole_0 = X1 ),
% 2.15/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1733,plain,
% 2.15/0.97      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
% 2.15/0.97      | k1_xboole_0 = X3
% 2.15/0.97      | k1_xboole_0 = X0
% 2.15/0.97      | k1_xboole_0 = X1
% 2.15/0.97      | k1_xboole_0 = X2
% 2.15/0.97      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_2817,plain,
% 2.15/0.97      ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
% 2.15/0.97      | sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0 ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_1728,c_1733]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_6,plain,
% 2.15/0.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.15/0.97      | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 2.15/0.97      | k1_xboole_0 = X4
% 2.15/0.97      | k1_xboole_0 = X3
% 2.15/0.97      | k1_xboole_0 = X2
% 2.15/0.97      | k1_xboole_0 = X1 ),
% 2.15/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1732,plain,
% 2.15/0.97      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 2.15/0.97      | k1_xboole_0 = X3
% 2.15/0.97      | k1_xboole_0 = X0
% 2.15/0.97      | k1_xboole_0 = X1
% 2.15/0.97      | k1_xboole_0 = X2
% 2.15/0.97      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_4432,plain,
% 2.15/0.97      ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 2.15/0.97      | sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0 ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_1728,c_1732]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_7,plain,
% 2.15/0.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.15/0.97      | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 2.15/0.97      | k1_xboole_0 = X4
% 2.15/0.97      | k1_xboole_0 = X3
% 2.15/0.97      | k1_xboole_0 = X2
% 2.15/0.97      | k1_xboole_0 = X1 ),
% 2.15/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1731,plain,
% 2.15/0.97      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 2.15/0.97      | k1_xboole_0 = X3
% 2.15/0.97      | k1_xboole_0 = X0
% 2.15/0.97      | k1_xboole_0 = X1
% 2.15/0.97      | k1_xboole_0 = X2
% 2.15/0.97      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_2267,plain,
% 2.15/0.97      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 2.15/0.97      | sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0 ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_1728,c_1731]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_8,negated_conjecture,
% 2.15/0.97      ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
% 2.15/0.97      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
% 2.15/0.97      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
% 2.15/0.97      | ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
% 2.15/0.97      inference(cnf_transformation,[],[f36]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1730,plain,
% 2.15/0.97      ( r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) != iProver_top
% 2.15/0.97      | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
% 2.15/0.97      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.15/0.97      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_3779,plain,
% 2.15/0.97      ( sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
% 2.15/0.97      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.15/0.97      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.15/0.97      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) != iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_2267,c_1730]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_20,plain,
% 2.15/0.97      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1854,plain,
% 2.15/0.97      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
% 2.15/0.97      | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
% 2.15/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1855,plain,
% 2.15/0.97      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
% 2.15/0.97      | r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) != iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_1854]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1901,plain,
% 2.15/0.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
% 2.15/0.97      | ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.15/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1905,plain,
% 2.15/0.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 2.15/0.97      | r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_1901]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_2055,plain,
% 2.15/0.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
% 2.15/0.97      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) ),
% 2.15/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_2059,plain,
% 2.15/0.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) = iProver_top
% 2.15/0.97      | r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_2055]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_4045,plain,
% 2.15/0.97      ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.15/0.97      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.15/0.97      | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK3 = k1_xboole_0 ),
% 2.15/0.97      inference(global_propositional_subsumption,
% 2.15/0.97                [status(thm)],
% 2.15/0.97                [c_3779,c_20,c_1855,c_1905,c_2059]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_4046,plain,
% 2.15/0.97      ( sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
% 2.15/0.97      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.15/0.97      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
% 2.15/0.97      inference(renaming,[status(thm)],[c_4045]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_5104,plain,
% 2.15/0.97      ( sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.15/0.97      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.15/0.97      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) != iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_4432,c_4046]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_2056,plain,
% 2.15/0.97      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
% 2.15/0.97      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
% 2.15/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_2057,plain,
% 2.15/0.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 2.15/0.97      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) = iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_2056]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_5107,plain,
% 2.15/0.97      ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.15/0.97      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK3 = k1_xboole_0 ),
% 2.15/0.97      inference(global_propositional_subsumption,
% 2.15/0.97                [status(thm)],
% 2.15/0.97                [c_5104,c_20,c_1855,c_1905,c_2057]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_5108,plain,
% 2.15/0.97      ( sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.15/0.97      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
% 2.15/0.97      inference(renaming,[status(thm)],[c_5107]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_5117,plain,
% 2.15/0.97      ( sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.15/0.97      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) != iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_2817,c_5108]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1902,plain,
% 2.15/0.97      ( ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
% 2.15/0.97      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
% 2.15/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1903,plain,
% 2.15/0.97      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top
% 2.15/0.97      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_1902]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_6098,plain,
% 2.15/0.97      ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK3 = k1_xboole_0 ),
% 2.15/0.97      inference(global_propositional_subsumption,
% 2.15/0.97                [status(thm)],
% 2.15/0.97                [c_5117,c_20,c_1855,c_1903]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_6099,plain,
% 2.15/0.97      ( sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
% 2.15/0.97      inference(renaming,[status(thm)],[c_6098]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_6107,plain,
% 2.15/0.97      ( sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | r2_hidden(k2_mcart_1(sK8),sK7) != iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_2385,c_6099]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1847,plain,
% 2.15/0.97      ( r2_hidden(k2_mcart_1(sK8),sK7)
% 2.15/0.97      | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
% 2.15/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_6108,plain,
% 2.15/0.97      ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
% 2.15/0.97      | sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0 ),
% 2.15/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_6107]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_6110,plain,
% 2.15/0.97      ( sK0 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK3 = k1_xboole_0 ),
% 2.15/0.97      inference(global_propositional_subsumption,
% 2.15/0.97                [status(thm)],
% 2.15/0.97                [c_6107,c_20,c_1848]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_6111,plain,
% 2.15/0.97      ( sK3 = k1_xboole_0
% 2.15/0.97      | sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0 ),
% 2.15/0.97      inference(renaming,[status(thm)],[c_6110]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_11,negated_conjecture,
% 2.15/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
% 2.15/0.97      inference(cnf_transformation,[],[f33]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1727,plain,
% 2.15/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_6122,plain,
% 2.15/0.97      ( sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_6111,c_1727]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_0,plain,
% 2.15/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 2.15/0.97      inference(cnf_transformation,[],[f20]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1,plain,
% 2.15/0.97      ( ~ r2_hidden(X0,X1)
% 2.15/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.15/0.97      | ~ v1_xboole_0(X2) ),
% 2.15/0.97      inference(cnf_transformation,[],[f21]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_165,plain,
% 2.15/0.97      ( ~ r2_hidden(X0,X1)
% 2.15/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.15/0.97      | k1_xboole_0 != X2 ),
% 2.15/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_166,plain,
% 2.15/0.97      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 2.15/0.97      inference(unflattening,[status(thm)],[c_165]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1723,plain,
% 2.15/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.15/0.97      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_166]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_6971,plain,
% 2.15/0.97      ( sK2 = k1_xboole_0
% 2.15/0.97      | sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | r2_hidden(X0,sK7) != iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_6122,c_1723]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_8167,plain,
% 2.15/0.97      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_2376,c_6971]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_12,negated_conjecture,
% 2.15/0.97      ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
% 2.15/0.97      inference(cnf_transformation,[],[f32]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1726,plain,
% 2.15/0.97      ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_8833,plain,
% 2.15/0.97      ( sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_8167,c_1726]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_8865,plain,
% 2.15/0.97      ( sK1 = k1_xboole_0
% 2.15/0.97      | sK0 = k1_xboole_0
% 2.15/0.97      | r2_hidden(X0,sK6) != iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_8833,c_1723]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_9076,plain,
% 2.15/0.97      ( sK1 = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_3321,c_8865]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_13,negated_conjecture,
% 2.15/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
% 2.15/0.97      inference(cnf_transformation,[],[f31]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1725,plain,
% 2.15/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_9085,plain,
% 2.15/0.97      ( sK0 = k1_xboole_0
% 2.15/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_9076,c_1725]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_9131,plain,
% 2.15/0.97      ( sK0 = k1_xboole_0 | r2_hidden(X0,sK5) != iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_9085,c_1723]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_9147,plain,
% 2.15/0.97      ( sK0 = k1_xboole_0 ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_4417,c_9131]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_14,negated_conjecture,
% 2.15/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
% 2.15/0.97      inference(cnf_transformation,[],[f30]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_1724,plain,
% 2.15/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.15/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_9329,plain,
% 2.15/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.15/0.97      inference(demodulation,[status(thm)],[c_9147,c_1724]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_9347,plain,
% 2.15/0.97      ( r2_hidden(X0,sK4) != iProver_top ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_9329,c_1723]) ).
% 2.15/0.97  
% 2.15/0.97  cnf(c_10258,plain,
% 2.15/0.97      ( $false ),
% 2.15/0.97      inference(superposition,[status(thm)],[c_4418,c_9347]) ).
% 2.15/0.97  
% 2.15/0.97  
% 2.15/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.15/0.97  
% 2.15/0.97  ------                               Statistics
% 2.15/0.97  
% 2.15/0.97  ------ General
% 2.15/0.97  
% 2.15/0.97  abstr_ref_over_cycles:                  0
% 2.15/0.97  abstr_ref_under_cycles:                 0
% 2.15/0.97  gc_basic_clause_elim:                   0
% 2.15/0.97  forced_gc_time:                         0
% 2.15/0.97  parsing_time:                           0.008
% 2.15/0.97  unif_index_cands_time:                  0.
% 2.15/0.97  unif_index_add_time:                    0.
% 2.15/0.97  orderings_time:                         0.
% 2.15/0.97  out_proof_time:                         0.008
% 2.15/0.97  total_time:                             0.383
% 2.15/0.97  num_of_symbols:                         52
% 2.15/0.97  num_of_terms:                           15796
% 2.15/0.97  
% 2.15/0.97  ------ Preprocessing
% 2.15/0.97  
% 2.15/0.97  num_of_splits:                          0
% 2.15/0.97  num_of_split_atoms:                     0
% 2.15/0.97  num_of_reused_defs:                     0
% 2.15/0.97  num_eq_ax_congr_red:                    0
% 2.15/0.97  num_of_sem_filtered_clauses:            1
% 2.15/0.97  num_of_subtypes:                        0
% 2.15/0.97  monotx_restored_types:                  0
% 2.15/0.97  sat_num_of_epr_types:                   0
% 2.15/0.97  sat_num_of_non_cyclic_types:            0
% 2.15/0.97  sat_guarded_non_collapsed_types:        0
% 2.15/0.97  num_pure_diseq_elim:                    0
% 2.15/0.97  simp_replaced_by:                       0
% 2.15/0.97  res_preprocessed:                       82
% 2.15/0.97  prep_upred:                             0
% 2.15/0.97  prep_unflattend:                        51
% 2.15/0.97  smt_new_axioms:                         0
% 2.15/0.97  pred_elim_cands:                        2
% 2.15/0.97  pred_elim:                              1
% 2.15/0.97  pred_elim_cl:                           1
% 2.15/0.97  pred_elim_cycles:                       3
% 2.15/0.97  merged_defs:                            0
% 2.15/0.97  merged_defs_ncl:                        0
% 2.15/0.97  bin_hyper_res:                          0
% 2.15/0.97  prep_cycles:                            4
% 2.15/0.97  pred_elim_time:                         0.019
% 2.15/0.97  splitting_time:                         0.
% 2.15/0.97  sem_filter_time:                        0.
% 2.15/0.97  monotx_time:                            0.
% 2.15/0.97  subtype_inf_time:                       0.
% 2.15/0.97  
% 2.15/0.97  ------ Problem properties
% 2.15/0.97  
% 2.15/0.97  clauses:                                14
% 2.15/0.97  conjectures:                            7
% 2.15/0.97  epr:                                    0
% 2.15/0.97  horn:                                   10
% 2.15/0.97  ground:                                 7
% 2.15/0.97  unary:                                  6
% 2.15/0.97  binary:                                 3
% 2.15/0.97  lits:                                   40
% 2.15/0.97  lits_eq:                                20
% 2.15/0.97  fd_pure:                                0
% 2.15/0.97  fd_pseudo:                              0
% 2.15/0.97  fd_cond:                                4
% 2.15/0.97  fd_pseudo_cond:                         0
% 2.15/0.97  ac_symbols:                             0
% 2.15/0.97  
% 2.15/0.97  ------ Propositional Solver
% 2.15/0.97  
% 2.15/0.97  prop_solver_calls:                      29
% 2.15/0.97  prop_fast_solver_calls:                 940
% 2.15/0.97  smt_solver_calls:                       0
% 2.15/0.97  smt_fast_solver_calls:                  0
% 2.15/0.97  prop_num_of_clauses:                    2951
% 2.15/0.97  prop_preprocess_simplified:             10980
% 2.15/0.97  prop_fo_subsumed:                       4
% 2.15/0.97  prop_solver_time:                       0.
% 2.15/0.97  smt_solver_time:                        0.
% 2.15/0.97  smt_fast_solver_time:                   0.
% 2.15/0.97  prop_fast_solver_time:                  0.
% 2.15/0.97  prop_unsat_core_time:                   0.
% 2.15/0.97  
% 2.15/0.97  ------ QBF
% 2.15/0.97  
% 2.15/0.97  qbf_q_res:                              0
% 2.15/0.97  qbf_num_tautologies:                    0
% 2.15/0.97  qbf_prep_cycles:                        0
% 2.15/0.97  
% 2.15/0.97  ------ BMC1
% 2.15/0.97  
% 2.15/0.97  bmc1_current_bound:                     -1
% 2.15/0.97  bmc1_last_solved_bound:                 -1
% 2.15/0.97  bmc1_unsat_core_size:                   -1
% 2.15/0.97  bmc1_unsat_core_parents_size:           -1
% 2.15/0.97  bmc1_merge_next_fun:                    0
% 2.15/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.15/0.97  
% 2.15/0.97  ------ Instantiation
% 2.15/0.97  
% 2.15/0.97  inst_num_of_clauses:                    1144
% 2.15/0.97  inst_num_in_passive:                    678
% 2.15/0.97  inst_num_in_active:                     235
% 2.15/0.97  inst_num_in_unprocessed:                231
% 2.15/0.97  inst_num_of_loops:                      240
% 2.15/0.97  inst_num_of_learning_restarts:          0
% 2.15/0.97  inst_num_moves_active_passive:          4
% 2.15/0.97  inst_lit_activity:                      0
% 2.15/0.97  inst_lit_activity_moves:                0
% 2.15/0.97  inst_num_tautologies:                   0
% 2.15/0.97  inst_num_prop_implied:                  0
% 2.15/0.97  inst_num_existing_simplified:           0
% 2.15/0.97  inst_num_eq_res_simplified:             0
% 2.15/0.97  inst_num_child_elim:                    0
% 2.15/0.97  inst_num_of_dismatching_blockings:      27
% 2.15/0.97  inst_num_of_non_proper_insts:           793
% 2.15/0.97  inst_num_of_duplicates:                 0
% 2.15/0.97  inst_inst_num_from_inst_to_res:         0
% 2.15/0.97  inst_dismatching_checking_time:         0.
% 2.15/0.97  
% 2.15/0.97  ------ Resolution
% 2.15/0.97  
% 2.15/0.97  res_num_of_clauses:                     0
% 2.15/0.97  res_num_in_passive:                     0
% 2.15/0.97  res_num_in_active:                      0
% 2.15/0.97  res_num_of_loops:                       86
% 2.15/0.97  res_forward_subset_subsumed:            24
% 2.15/0.97  res_backward_subset_subsumed:           0
% 2.15/0.97  res_forward_subsumed:                   0
% 2.15/0.97  res_backward_subsumed:                  0
% 2.15/0.97  res_forward_subsumption_resolution:     0
% 2.15/0.97  res_backward_subsumption_resolution:    0
% 2.15/0.97  res_clause_to_clause_subsumption:       33
% 2.15/0.97  res_orphan_elimination:                 0
% 2.15/0.97  res_tautology_del:                      21
% 2.15/0.97  res_num_eq_res_simplified:              0
% 2.15/0.97  res_num_sel_changes:                    0
% 2.15/0.97  res_moves_from_active_to_pass:          0
% 2.15/0.97  
% 2.15/0.97  ------ Superposition
% 2.15/0.97  
% 2.15/0.97  sup_time_total:                         0.
% 2.15/0.97  sup_time_generating:                    0.
% 2.15/0.97  sup_time_sim_full:                      0.
% 2.15/0.97  sup_time_sim_immed:                     0.
% 2.15/0.97  
% 2.15/0.97  sup_num_of_clauses:                     25
% 2.15/0.97  sup_num_in_active:                      25
% 2.15/0.97  sup_num_in_passive:                     0
% 2.15/0.97  sup_num_of_loops:                       46
% 2.15/0.97  sup_fw_superposition:                   29
% 2.15/0.97  sup_bw_superposition:                   47
% 2.15/0.97  sup_immediate_simplified:               30
% 2.15/0.97  sup_given_eliminated:                   0
% 2.15/0.97  comparisons_done:                       0
% 2.15/0.97  comparisons_avoided:                    60
% 2.15/0.97  
% 2.15/0.97  ------ Simplifications
% 2.15/0.97  
% 2.15/0.97  
% 2.15/0.97  sim_fw_subset_subsumed:                 27
% 2.15/0.97  sim_bw_subset_subsumed:                 21
% 2.15/0.97  sim_fw_subsumed:                        0
% 2.15/0.97  sim_bw_subsumed:                        0
% 2.15/0.97  sim_fw_subsumption_res:                 0
% 2.15/0.97  sim_bw_subsumption_res:                 0
% 2.15/0.97  sim_tautology_del:                      0
% 2.15/0.97  sim_eq_tautology_del:                   20
% 2.15/0.97  sim_eq_res_simp:                        0
% 2.15/0.97  sim_fw_demodulated:                     0
% 2.15/0.97  sim_bw_demodulated:                     7
% 2.15/0.97  sim_light_normalised:                   0
% 2.15/0.97  sim_joinable_taut:                      0
% 2.15/0.97  sim_joinable_simp:                      0
% 2.15/0.97  sim_ac_normalised:                      0
% 2.15/0.97  sim_smt_subsumption:                    0
% 2.15/0.97  
%------------------------------------------------------------------------------
