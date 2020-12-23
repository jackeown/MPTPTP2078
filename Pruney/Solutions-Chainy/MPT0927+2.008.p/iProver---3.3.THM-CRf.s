%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:31 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1920)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f14])).

fof(f20,plain,(
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

fof(f19,plain,(
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

fof(f18,plain,(
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

fof(f17,plain,(
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

fof(f16,plain,
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

fof(f21,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f15,f20,f19,f18,f17,f16])).

fof(f38,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f45,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f7,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f39,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1794,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1800,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2262,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1800])).

cnf(c_2872,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2262,c_1800])).

cnf(c_4868,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_1800])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1801,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4867,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_1801])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1793,plain,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1799,plain,
    ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2561,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1793,c_1799])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1798,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4619,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1793,c_1798])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1797,plain,
    ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4196,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1793,c_1797])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1796,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2258,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1793,c_1796])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1795,plain,
    ( r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) != iProver_top
    | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4187,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2258,c_1795])).

cnf(c_21,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1926,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1927,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
    | r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1926])).

cnf(c_1988,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1992,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1988])).

cnf(c_2179,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2183,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) = iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2179])).

cnf(c_5480,plain,
    ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
    | sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4187,c_21,c_1927,c_1992,c_2183])).

cnf(c_5481,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5480])).

cnf(c_5491,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4196,c_5481])).

cnf(c_2180,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2181,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2180])).

cnf(c_7474,plain,
    ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5491,c_21,c_1927,c_1992,c_2181])).

cnf(c_7475,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_7474])).

cnf(c_7484,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4619,c_7475])).

cnf(c_1989,plain,
    ( ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1990,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1989])).

cnf(c_7487,plain,
    ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
    | sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7484,c_21,c_1927,c_1990])).

cnf(c_7488,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_7487])).

cnf(c_7496,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK8),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2561,c_7488])).

cnf(c_1919,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7)
    | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7497,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7496])).

cnf(c_9518,plain,
    ( sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7496,c_21,c_1920])).

cnf(c_9519,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9518])).

cnf(c_9530,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9519,c_1793])).

cnf(c_2370,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1801])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1792,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1802,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2376,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1792,c_1802])).

cnf(c_2882,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2370,c_2376])).

cnf(c_9524,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK8),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9519,c_2882])).

cnf(c_9570,plain,
    ( r2_hidden(k2_mcart_1(sK8),k1_xboole_0)
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9524])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_177,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_178,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_9681,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_9751,plain,
    ( sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9530,c_12,c_10,c_1547,c_1919,c_2208,c_3325,c_9519,c_9645,c_9643,c_9681])).

cnf(c_9752,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9751])).

cnf(c_2871,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2262,c_1801])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1791,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2377,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1791,c_1802])).

cnf(c_4622,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2871,c_2377])).

cnf(c_9756,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9752,c_4622])).

cnf(c_1788,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_178])).

cnf(c_10036,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9756,c_1788])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1790,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10044,plain,
    ( sK0 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10036,c_1790])).

cnf(c_10095,plain,
    ( sK0 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10044,c_1802])).

cnf(c_179,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_178])).

cnf(c_10109,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10095,c_179])).

cnf(c_10110,plain,
    ( sK0 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_10109])).

cnf(c_10117,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4867,c_10110])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1789,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2379,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_1802])).

cnf(c_10124,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10117,c_2379])).

cnf(c_10364,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10124,c_179])).

cnf(c_10371,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4868,c_10364])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.50/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.50/0.99  
% 2.50/0.99  ------  iProver source info
% 2.50/0.99  
% 2.50/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.50/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.50/0.99  git: non_committed_changes: false
% 2.50/0.99  git: last_make_outside_of_git: false
% 2.50/0.99  
% 2.50/0.99  ------ 
% 2.50/0.99  
% 2.50/0.99  ------ Input Options
% 2.50/0.99  
% 2.50/0.99  --out_options                           all
% 2.50/0.99  --tptp_safe_out                         true
% 2.50/0.99  --problem_path                          ""
% 2.50/0.99  --include_path                          ""
% 2.50/0.99  --clausifier                            res/vclausify_rel
% 2.50/0.99  --clausifier_options                    --mode clausify
% 2.50/0.99  --stdin                                 false
% 2.50/0.99  --stats_out                             all
% 2.50/0.99  
% 2.50/0.99  ------ General Options
% 2.50/0.99  
% 2.50/0.99  --fof                                   false
% 2.50/0.99  --time_out_real                         305.
% 2.50/0.99  --time_out_virtual                      -1.
% 2.50/0.99  --symbol_type_check                     false
% 2.50/0.99  --clausify_out                          false
% 2.50/0.99  --sig_cnt_out                           false
% 2.50/0.99  --trig_cnt_out                          false
% 2.50/0.99  --trig_cnt_out_tolerance                1.
% 2.50/0.99  --trig_cnt_out_sk_spl                   false
% 2.50/0.99  --abstr_cl_out                          false
% 2.50/0.99  
% 2.50/0.99  ------ Global Options
% 2.50/0.99  
% 2.50/0.99  --schedule                              default
% 2.50/0.99  --add_important_lit                     false
% 2.50/0.99  --prop_solver_per_cl                    1000
% 2.50/0.99  --min_unsat_core                        false
% 2.50/0.99  --soft_assumptions                      false
% 2.50/0.99  --soft_lemma_size                       3
% 2.50/0.99  --prop_impl_unit_size                   0
% 2.50/0.99  --prop_impl_unit                        []
% 2.50/0.99  --share_sel_clauses                     true
% 2.50/0.99  --reset_solvers                         false
% 2.50/0.99  --bc_imp_inh                            [conj_cone]
% 2.50/0.99  --conj_cone_tolerance                   3.
% 2.50/0.99  --extra_neg_conj                        none
% 2.50/0.99  --large_theory_mode                     true
% 2.50/0.99  --prolific_symb_bound                   200
% 2.50/0.99  --lt_threshold                          2000
% 2.50/0.99  --clause_weak_htbl                      true
% 2.50/0.99  --gc_record_bc_elim                     false
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing Options
% 2.50/0.99  
% 2.50/0.99  --preprocessing_flag                    true
% 2.50/0.99  --time_out_prep_mult                    0.1
% 2.50/0.99  --splitting_mode                        input
% 2.50/0.99  --splitting_grd                         true
% 2.50/0.99  --splitting_cvd                         false
% 2.50/0.99  --splitting_cvd_svl                     false
% 2.50/0.99  --splitting_nvd                         32
% 2.50/0.99  --sub_typing                            true
% 2.50/0.99  --prep_gs_sim                           true
% 2.50/0.99  --prep_unflatten                        true
% 2.50/0.99  --prep_res_sim                          true
% 2.50/0.99  --prep_upred                            true
% 2.50/0.99  --prep_sem_filter                       exhaustive
% 2.50/0.99  --prep_sem_filter_out                   false
% 2.50/0.99  --pred_elim                             true
% 2.50/0.99  --res_sim_input                         true
% 2.50/0.99  --eq_ax_congr_red                       true
% 2.50/0.99  --pure_diseq_elim                       true
% 2.50/0.99  --brand_transform                       false
% 2.50/0.99  --non_eq_to_eq                          false
% 2.50/0.99  --prep_def_merge                        true
% 2.50/0.99  --prep_def_merge_prop_impl              false
% 2.50/0.99  --prep_def_merge_mbd                    true
% 2.50/0.99  --prep_def_merge_tr_red                 false
% 2.50/0.99  --prep_def_merge_tr_cl                  false
% 2.50/0.99  --smt_preprocessing                     true
% 2.50/0.99  --smt_ac_axioms                         fast
% 2.50/0.99  --preprocessed_out                      false
% 2.50/0.99  --preprocessed_stats                    false
% 2.50/0.99  
% 2.50/0.99  ------ Abstraction refinement Options
% 2.50/0.99  
% 2.50/0.99  --abstr_ref                             []
% 2.50/0.99  --abstr_ref_prep                        false
% 2.50/0.99  --abstr_ref_until_sat                   false
% 2.50/0.99  --abstr_ref_sig_restrict                funpre
% 2.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.99  --abstr_ref_under                       []
% 2.50/0.99  
% 2.50/0.99  ------ SAT Options
% 2.50/0.99  
% 2.50/0.99  --sat_mode                              false
% 2.50/0.99  --sat_fm_restart_options                ""
% 2.50/0.99  --sat_gr_def                            false
% 2.50/0.99  --sat_epr_types                         true
% 2.50/0.99  --sat_non_cyclic_types                  false
% 2.50/0.99  --sat_finite_models                     false
% 2.50/0.99  --sat_fm_lemmas                         false
% 2.50/0.99  --sat_fm_prep                           false
% 2.50/0.99  --sat_fm_uc_incr                        true
% 2.50/0.99  --sat_out_model                         small
% 2.50/0.99  --sat_out_clauses                       false
% 2.50/0.99  
% 2.50/0.99  ------ QBF Options
% 2.50/0.99  
% 2.50/0.99  --qbf_mode                              false
% 2.50/0.99  --qbf_elim_univ                         false
% 2.50/0.99  --qbf_dom_inst                          none
% 2.50/0.99  --qbf_dom_pre_inst                      false
% 2.50/0.99  --qbf_sk_in                             false
% 2.50/0.99  --qbf_pred_elim                         true
% 2.50/0.99  --qbf_split                             512
% 2.50/0.99  
% 2.50/0.99  ------ BMC1 Options
% 2.50/0.99  
% 2.50/0.99  --bmc1_incremental                      false
% 2.50/0.99  --bmc1_axioms                           reachable_all
% 2.50/0.99  --bmc1_min_bound                        0
% 2.50/0.99  --bmc1_max_bound                        -1
% 2.50/0.99  --bmc1_max_bound_default                -1
% 2.50/0.99  --bmc1_symbol_reachability              true
% 2.50/0.99  --bmc1_property_lemmas                  false
% 2.50/0.99  --bmc1_k_induction                      false
% 2.50/0.99  --bmc1_non_equiv_states                 false
% 2.50/0.99  --bmc1_deadlock                         false
% 2.50/0.99  --bmc1_ucm                              false
% 2.50/0.99  --bmc1_add_unsat_core                   none
% 2.50/0.99  --bmc1_unsat_core_children              false
% 2.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.99  --bmc1_out_stat                         full
% 2.50/0.99  --bmc1_ground_init                      false
% 2.50/0.99  --bmc1_pre_inst_next_state              false
% 2.50/0.99  --bmc1_pre_inst_state                   false
% 2.50/0.99  --bmc1_pre_inst_reach_state             false
% 2.50/0.99  --bmc1_out_unsat_core                   false
% 2.50/0.99  --bmc1_aig_witness_out                  false
% 2.50/0.99  --bmc1_verbose                          false
% 2.50/0.99  --bmc1_dump_clauses_tptp                false
% 2.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.99  --bmc1_dump_file                        -
% 2.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.99  --bmc1_ucm_extend_mode                  1
% 2.50/0.99  --bmc1_ucm_init_mode                    2
% 2.50/0.99  --bmc1_ucm_cone_mode                    none
% 2.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.99  --bmc1_ucm_relax_model                  4
% 2.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.99  --bmc1_ucm_layered_model                none
% 2.50/0.99  --bmc1_ucm_max_lemma_size               10
% 2.50/0.99  
% 2.50/0.99  ------ AIG Options
% 2.50/0.99  
% 2.50/0.99  --aig_mode                              false
% 2.50/0.99  
% 2.50/0.99  ------ Instantiation Options
% 2.50/0.99  
% 2.50/0.99  --instantiation_flag                    true
% 2.50/0.99  --inst_sos_flag                         false
% 2.50/0.99  --inst_sos_phase                        true
% 2.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel_side                     num_symb
% 2.50/0.99  --inst_solver_per_active                1400
% 2.50/0.99  --inst_solver_calls_frac                1.
% 2.50/0.99  --inst_passive_queue_type               priority_queues
% 2.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.99  --inst_passive_queues_freq              [25;2]
% 2.50/0.99  --inst_dismatching                      true
% 2.50/0.99  --inst_eager_unprocessed_to_passive     true
% 2.50/0.99  --inst_prop_sim_given                   true
% 2.50/0.99  --inst_prop_sim_new                     false
% 2.50/0.99  --inst_subs_new                         false
% 2.50/0.99  --inst_eq_res_simp                      false
% 2.50/0.99  --inst_subs_given                       false
% 2.50/0.99  --inst_orphan_elimination               true
% 2.50/0.99  --inst_learning_loop_flag               true
% 2.50/0.99  --inst_learning_start                   3000
% 2.50/0.99  --inst_learning_factor                  2
% 2.50/0.99  --inst_start_prop_sim_after_learn       3
% 2.50/0.99  --inst_sel_renew                        solver
% 2.50/0.99  --inst_lit_activity_flag                true
% 2.50/0.99  --inst_restr_to_given                   false
% 2.50/0.99  --inst_activity_threshold               500
% 2.50/0.99  --inst_out_proof                        true
% 2.50/0.99  
% 2.50/0.99  ------ Resolution Options
% 2.50/0.99  
% 2.50/0.99  --resolution_flag                       true
% 2.50/0.99  --res_lit_sel                           adaptive
% 2.50/0.99  --res_lit_sel_side                      none
% 2.50/0.99  --res_ordering                          kbo
% 2.50/0.99  --res_to_prop_solver                    active
% 2.50/0.99  --res_prop_simpl_new                    false
% 2.50/0.99  --res_prop_simpl_given                  true
% 2.50/0.99  --res_passive_queue_type                priority_queues
% 2.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.99  --res_passive_queues_freq               [15;5]
% 2.50/0.99  --res_forward_subs                      full
% 2.50/0.99  --res_backward_subs                     full
% 2.50/0.99  --res_forward_subs_resolution           true
% 2.50/0.99  --res_backward_subs_resolution          true
% 2.50/0.99  --res_orphan_elimination                true
% 2.50/0.99  --res_time_limit                        2.
% 2.50/0.99  --res_out_proof                         true
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Options
% 2.50/0.99  
% 2.50/0.99  --superposition_flag                    true
% 2.50/0.99  --sup_passive_queue_type                priority_queues
% 2.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.99  --demod_completeness_check              fast
% 2.50/0.99  --demod_use_ground                      true
% 2.50/0.99  --sup_to_prop_solver                    passive
% 2.50/0.99  --sup_prop_simpl_new                    true
% 2.50/0.99  --sup_prop_simpl_given                  true
% 2.50/0.99  --sup_fun_splitting                     false
% 2.50/0.99  --sup_smt_interval                      50000
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Simplification Setup
% 2.50/0.99  
% 2.50/0.99  --sup_indices_passive                   []
% 2.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_full_bw                           [BwDemod]
% 2.50/0.99  --sup_immed_triv                        [TrivRules]
% 2.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_immed_bw_main                     []
% 2.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  
% 2.50/0.99  ------ Combination Options
% 2.50/0.99  
% 2.50/0.99  --comb_res_mult                         3
% 2.50/0.99  --comb_sup_mult                         2
% 2.50/0.99  --comb_inst_mult                        10
% 2.50/0.99  
% 2.50/0.99  ------ Debug Options
% 2.50/0.99  
% 2.50/0.99  --dbg_backtrace                         false
% 2.50/0.99  --dbg_dump_prop_clauses                 false
% 2.50/0.99  --dbg_dump_prop_clauses_file            -
% 2.50/0.99  --dbg_out_stat                          false
% 2.50/0.99  ------ Parsing...
% 2.50/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.50/0.99  ------ Proving...
% 2.50/0.99  ------ Problem Properties 
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  clauses                                 15
% 2.50/0.99  conjectures                             7
% 2.50/0.99  EPR                                     1
% 2.50/0.99  Horn                                    11
% 2.50/0.99  unary                                   7
% 2.50/0.99  binary                                  2
% 2.50/0.99  lits                                    42
% 2.50/0.99  lits eq                                 20
% 2.50/0.99  fd_pure                                 0
% 2.50/0.99  fd_pseudo                               0
% 2.50/0.99  fd_cond                                 4
% 2.50/0.99  fd_pseudo_cond                          0
% 2.50/0.99  AC symbols                              0
% 2.50/0.99  
% 2.50/0.99  ------ Schedule dynamic 5 is on 
% 2.50/0.99  
% 2.50/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  ------ 
% 2.50/0.99  Current options:
% 2.50/0.99  ------ 
% 2.50/0.99  
% 2.50/0.99  ------ Input Options
% 2.50/0.99  
% 2.50/0.99  --out_options                           all
% 2.50/0.99  --tptp_safe_out                         true
% 2.50/0.99  --problem_path                          ""
% 2.50/0.99  --include_path                          ""
% 2.50/0.99  --clausifier                            res/vclausify_rel
% 2.50/0.99  --clausifier_options                    --mode clausify
% 2.50/0.99  --stdin                                 false
% 2.50/0.99  --stats_out                             all
% 2.50/0.99  
% 2.50/0.99  ------ General Options
% 2.50/0.99  
% 2.50/0.99  --fof                                   false
% 2.50/0.99  --time_out_real                         305.
% 2.50/0.99  --time_out_virtual                      -1.
% 2.50/0.99  --symbol_type_check                     false
% 2.50/0.99  --clausify_out                          false
% 2.50/0.99  --sig_cnt_out                           false
% 2.50/0.99  --trig_cnt_out                          false
% 2.50/0.99  --trig_cnt_out_tolerance                1.
% 2.50/0.99  --trig_cnt_out_sk_spl                   false
% 2.50/0.99  --abstr_cl_out                          false
% 2.50/0.99  
% 2.50/0.99  ------ Global Options
% 2.50/0.99  
% 2.50/0.99  --schedule                              default
% 2.50/0.99  --add_important_lit                     false
% 2.50/0.99  --prop_solver_per_cl                    1000
% 2.50/0.99  --min_unsat_core                        false
% 2.50/0.99  --soft_assumptions                      false
% 2.50/0.99  --soft_lemma_size                       3
% 2.50/0.99  --prop_impl_unit_size                   0
% 2.50/0.99  --prop_impl_unit                        []
% 2.50/0.99  --share_sel_clauses                     true
% 2.50/0.99  --reset_solvers                         false
% 2.50/0.99  --bc_imp_inh                            [conj_cone]
% 2.50/0.99  --conj_cone_tolerance                   3.
% 2.50/0.99  --extra_neg_conj                        none
% 2.50/0.99  --large_theory_mode                     true
% 2.50/0.99  --prolific_symb_bound                   200
% 2.50/0.99  --lt_threshold                          2000
% 2.50/0.99  --clause_weak_htbl                      true
% 2.50/0.99  --gc_record_bc_elim                     false
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing Options
% 2.50/0.99  
% 2.50/0.99  --preprocessing_flag                    true
% 2.50/0.99  --time_out_prep_mult                    0.1
% 2.50/0.99  --splitting_mode                        input
% 2.50/0.99  --splitting_grd                         true
% 2.50/0.99  --splitting_cvd                         false
% 2.50/0.99  --splitting_cvd_svl                     false
% 2.50/0.99  --splitting_nvd                         32
% 2.50/0.99  --sub_typing                            true
% 2.50/0.99  --prep_gs_sim                           true
% 2.50/0.99  --prep_unflatten                        true
% 2.50/0.99  --prep_res_sim                          true
% 2.50/0.99  --prep_upred                            true
% 2.50/0.99  --prep_sem_filter                       exhaustive
% 2.50/0.99  --prep_sem_filter_out                   false
% 2.50/0.99  --pred_elim                             true
% 2.50/0.99  --res_sim_input                         true
% 2.50/0.99  --eq_ax_congr_red                       true
% 2.50/0.99  --pure_diseq_elim                       true
% 2.50/0.99  --brand_transform                       false
% 2.50/0.99  --non_eq_to_eq                          false
% 2.50/0.99  --prep_def_merge                        true
% 2.50/0.99  --prep_def_merge_prop_impl              false
% 2.50/0.99  --prep_def_merge_mbd                    true
% 2.50/0.99  --prep_def_merge_tr_red                 false
% 2.50/0.99  --prep_def_merge_tr_cl                  false
% 2.50/0.99  --smt_preprocessing                     true
% 2.50/0.99  --smt_ac_axioms                         fast
% 2.50/0.99  --preprocessed_out                      false
% 2.50/0.99  --preprocessed_stats                    false
% 2.50/0.99  
% 2.50/0.99  ------ Abstraction refinement Options
% 2.50/0.99  
% 2.50/0.99  --abstr_ref                             []
% 2.50/0.99  --abstr_ref_prep                        false
% 2.50/0.99  --abstr_ref_until_sat                   false
% 2.50/0.99  --abstr_ref_sig_restrict                funpre
% 2.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.99  --abstr_ref_under                       []
% 2.50/0.99  
% 2.50/0.99  ------ SAT Options
% 2.50/0.99  
% 2.50/0.99  --sat_mode                              false
% 2.50/0.99  --sat_fm_restart_options                ""
% 2.50/0.99  --sat_gr_def                            false
% 2.50/0.99  --sat_epr_types                         true
% 2.50/0.99  --sat_non_cyclic_types                  false
% 2.50/0.99  --sat_finite_models                     false
% 2.50/0.99  --sat_fm_lemmas                         false
% 2.50/0.99  --sat_fm_prep                           false
% 2.50/0.99  --sat_fm_uc_incr                        true
% 2.50/0.99  --sat_out_model                         small
% 2.50/0.99  --sat_out_clauses                       false
% 2.50/0.99  
% 2.50/0.99  ------ QBF Options
% 2.50/0.99  
% 2.50/0.99  --qbf_mode                              false
% 2.50/0.99  --qbf_elim_univ                         false
% 2.50/0.99  --qbf_dom_inst                          none
% 2.50/0.99  --qbf_dom_pre_inst                      false
% 2.50/0.99  --qbf_sk_in                             false
% 2.50/0.99  --qbf_pred_elim                         true
% 2.50/0.99  --qbf_split                             512
% 2.50/0.99  
% 2.50/0.99  ------ BMC1 Options
% 2.50/0.99  
% 2.50/0.99  --bmc1_incremental                      false
% 2.50/0.99  --bmc1_axioms                           reachable_all
% 2.50/0.99  --bmc1_min_bound                        0
% 2.50/0.99  --bmc1_max_bound                        -1
% 2.50/0.99  --bmc1_max_bound_default                -1
% 2.50/0.99  --bmc1_symbol_reachability              true
% 2.50/0.99  --bmc1_property_lemmas                  false
% 2.50/0.99  --bmc1_k_induction                      false
% 2.50/0.99  --bmc1_non_equiv_states                 false
% 2.50/0.99  --bmc1_deadlock                         false
% 2.50/0.99  --bmc1_ucm                              false
% 2.50/0.99  --bmc1_add_unsat_core                   none
% 2.50/0.99  --bmc1_unsat_core_children              false
% 2.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.99  --bmc1_out_stat                         full
% 2.50/0.99  --bmc1_ground_init                      false
% 2.50/0.99  --bmc1_pre_inst_next_state              false
% 2.50/0.99  --bmc1_pre_inst_state                   false
% 2.50/0.99  --bmc1_pre_inst_reach_state             false
% 2.50/0.99  --bmc1_out_unsat_core                   false
% 2.50/0.99  --bmc1_aig_witness_out                  false
% 2.50/0.99  --bmc1_verbose                          false
% 2.50/0.99  --bmc1_dump_clauses_tptp                false
% 2.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.99  --bmc1_dump_file                        -
% 2.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.99  --bmc1_ucm_extend_mode                  1
% 2.50/0.99  --bmc1_ucm_init_mode                    2
% 2.50/0.99  --bmc1_ucm_cone_mode                    none
% 2.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.99  --bmc1_ucm_relax_model                  4
% 2.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.99  --bmc1_ucm_layered_model                none
% 2.50/0.99  --bmc1_ucm_max_lemma_size               10
% 2.50/0.99  
% 2.50/0.99  ------ AIG Options
% 2.50/0.99  
% 2.50/0.99  --aig_mode                              false
% 2.50/0.99  
% 2.50/0.99  ------ Instantiation Options
% 2.50/0.99  
% 2.50/0.99  --instantiation_flag                    true
% 2.50/0.99  --inst_sos_flag                         false
% 2.50/0.99  --inst_sos_phase                        true
% 2.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel_side                     none
% 2.50/0.99  --inst_solver_per_active                1400
% 2.50/0.99  --inst_solver_calls_frac                1.
% 2.50/0.99  --inst_passive_queue_type               priority_queues
% 2.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.99  --inst_passive_queues_freq              [25;2]
% 2.50/0.99  --inst_dismatching                      true
% 2.50/0.99  --inst_eager_unprocessed_to_passive     true
% 2.50/0.99  --inst_prop_sim_given                   true
% 2.50/0.99  --inst_prop_sim_new                     false
% 2.50/0.99  --inst_subs_new                         false
% 2.50/0.99  --inst_eq_res_simp                      false
% 2.50/0.99  --inst_subs_given                       false
% 2.50/0.99  --inst_orphan_elimination               true
% 2.50/0.99  --inst_learning_loop_flag               true
% 2.50/0.99  --inst_learning_start                   3000
% 2.50/0.99  --inst_learning_factor                  2
% 2.50/0.99  --inst_start_prop_sim_after_learn       3
% 2.50/0.99  --inst_sel_renew                        solver
% 2.50/0.99  --inst_lit_activity_flag                true
% 2.50/0.99  --inst_restr_to_given                   false
% 2.50/0.99  --inst_activity_threshold               500
% 2.50/0.99  --inst_out_proof                        true
% 2.50/0.99  
% 2.50/0.99  ------ Resolution Options
% 2.50/0.99  
% 2.50/0.99  --resolution_flag                       false
% 2.50/0.99  --res_lit_sel                           adaptive
% 2.50/0.99  --res_lit_sel_side                      none
% 2.50/0.99  --res_ordering                          kbo
% 2.50/0.99  --res_to_prop_solver                    active
% 2.50/0.99  --res_prop_simpl_new                    false
% 2.50/0.99  --res_prop_simpl_given                  true
% 2.50/0.99  --res_passive_queue_type                priority_queues
% 2.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.99  --res_passive_queues_freq               [15;5]
% 2.50/0.99  --res_forward_subs                      full
% 2.50/0.99  --res_backward_subs                     full
% 2.50/0.99  --res_forward_subs_resolution           true
% 2.50/0.99  --res_backward_subs_resolution          true
% 2.50/0.99  --res_orphan_elimination                true
% 2.50/0.99  --res_time_limit                        2.
% 2.50/0.99  --res_out_proof                         true
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Options
% 2.50/0.99  
% 2.50/0.99  --superposition_flag                    true
% 2.50/0.99  --sup_passive_queue_type                priority_queues
% 2.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.99  --demod_completeness_check              fast
% 2.50/0.99  --demod_use_ground                      true
% 2.50/0.99  --sup_to_prop_solver                    passive
% 2.50/0.99  --sup_prop_simpl_new                    true
% 2.50/0.99  --sup_prop_simpl_given                  true
% 2.50/0.99  --sup_fun_splitting                     false
% 2.50/0.99  --sup_smt_interval                      50000
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Simplification Setup
% 2.50/0.99  
% 2.50/0.99  --sup_indices_passive                   []
% 2.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_full_bw                           [BwDemod]
% 2.50/0.99  --sup_immed_triv                        [TrivRules]
% 2.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_immed_bw_main                     []
% 2.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  
% 2.50/0.99  ------ Combination Options
% 2.50/0.99  
% 2.50/0.99  --comb_res_mult                         3
% 2.50/0.99  --comb_sup_mult                         2
% 2.50/0.99  --comb_inst_mult                        10
% 2.50/0.99  
% 2.50/0.99  ------ Debug Options
% 2.50/0.99  
% 2.50/0.99  --dbg_backtrace                         false
% 2.50/0.99  --dbg_dump_prop_clauses                 false
% 2.50/0.99  --dbg_dump_prop_clauses_file            -
% 2.50/0.99  --dbg_out_stat                          false
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  ------ Proving...
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  % SZS status Theorem for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99   Resolution empty clause
% 2.50/0.99  
% 2.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  fof(f8,conjecture,(
% 2.50/0.99    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f9,negated_conjecture,(
% 2.50/0.99    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 2.50/0.99    inference(negated_conjecture,[],[f8])).
% 2.50/0.99  
% 2.50/0.99  fof(f14,plain,(
% 2.50/0.99    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 2.50/0.99    inference(ennf_transformation,[],[f9])).
% 2.50/0.99  
% 2.50/0.99  fof(f15,plain,(
% 2.50/0.99    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 2.50/0.99    inference(flattening,[],[f14])).
% 2.50/0.99  
% 2.50/0.99  fof(f20,plain,(
% 2.50/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) => ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,sK8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,sK8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,sK8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,sK8),X4)) & r2_hidden(sK8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(sK8,k4_zfmisc_1(X0,X1,X2,X3)))) )),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f19,plain,(
% 2.50/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),sK7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(X3)))) )),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f18,plain,(
% 2.50/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),sK6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(sK6,k1_zfmisc_1(X2)))) )),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f17,plain,(
% 2.50/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),sK5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f16,plain,(
% 2.50/0.99    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0)))),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f21,plain,(
% 2.50/0.99    (((((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 2.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f15,f20,f19,f18,f17,f16])).
% 2.50/0.99  
% 2.50/0.99  fof(f38,plain,(
% 2.50/0.99    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.50/0.99    inference(cnf_transformation,[],[f21])).
% 2.50/0.99  
% 2.50/0.99  fof(f5,axiom,(
% 2.50/0.99    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f26,plain,(
% 2.50/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f5])).
% 2.50/0.99  
% 2.50/0.99  fof(f4,axiom,(
% 2.50/0.99    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f25,plain,(
% 2.50/0.99    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f4])).
% 2.50/0.99  
% 2.50/0.99  fof(f40,plain,(
% 2.50/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.50/0.99    inference(definition_unfolding,[],[f26,f25])).
% 2.50/0.99  
% 2.50/0.99  fof(f45,plain,(
% 2.50/0.99    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 2.50/0.99    inference(definition_unfolding,[],[f38,f40])).
% 2.50/0.99  
% 2.50/0.99  fof(f6,axiom,(
% 2.50/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f12,plain,(
% 2.50/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.50/0.99    inference(ennf_transformation,[],[f6])).
% 2.50/0.99  
% 2.50/0.99  fof(f27,plain,(
% 2.50/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f12])).
% 2.50/0.99  
% 2.50/0.99  fof(f28,plain,(
% 2.50/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f12])).
% 2.50/0.99  
% 2.50/0.99  fof(f37,plain,(
% 2.50/0.99    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 2.50/0.99    inference(cnf_transformation,[],[f21])).
% 2.50/0.99  
% 2.50/0.99  fof(f46,plain,(
% 2.50/0.99    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 2.50/0.99    inference(definition_unfolding,[],[f37,f40])).
% 2.50/0.99  
% 2.50/0.99  fof(f7,axiom,(
% 2.50/0.99    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f13,plain,(
% 2.50/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.50/0.99    inference(ennf_transformation,[],[f7])).
% 2.50/0.99  
% 2.50/0.99  fof(f32,plain,(
% 2.50/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(cnf_transformation,[],[f13])).
% 2.50/0.99  
% 2.50/0.99  fof(f41,plain,(
% 2.50/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(definition_unfolding,[],[f32,f40])).
% 2.50/0.99  
% 2.50/0.99  fof(f31,plain,(
% 2.50/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(cnf_transformation,[],[f13])).
% 2.50/0.99  
% 2.50/0.99  fof(f42,plain,(
% 2.50/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(definition_unfolding,[],[f31,f40])).
% 2.50/0.99  
% 2.50/0.99  fof(f30,plain,(
% 2.50/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(cnf_transformation,[],[f13])).
% 2.50/0.99  
% 2.50/0.99  fof(f43,plain,(
% 2.50/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(definition_unfolding,[],[f30,f40])).
% 2.50/0.99  
% 2.50/0.99  fof(f29,plain,(
% 2.50/0.99    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(cnf_transformation,[],[f13])).
% 2.50/0.99  
% 2.50/0.99  fof(f44,plain,(
% 2.50/0.99    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.50/0.99    inference(definition_unfolding,[],[f29,f40])).
% 2.50/0.99  
% 2.50/0.99  fof(f39,plain,(
% 2.50/0.99    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 2.50/0.99    inference(cnf_transformation,[],[f21])).
% 2.50/0.99  
% 2.50/0.99  fof(f36,plain,(
% 2.50/0.99    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 2.50/0.99    inference(cnf_transformation,[],[f21])).
% 2.50/0.99  
% 2.50/0.99  fof(f2,axiom,(
% 2.50/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f10,plain,(
% 2.50/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.50/0.99    inference(ennf_transformation,[],[f2])).
% 2.50/0.99  
% 2.50/0.99  fof(f23,plain,(
% 2.50/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f10])).
% 2.50/0.99  
% 2.50/0.99  fof(f1,axiom,(
% 2.50/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f22,plain,(
% 2.50/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f1])).
% 2.50/0.99  
% 2.50/0.99  fof(f3,axiom,(
% 2.50/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f11,plain,(
% 2.50/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.50/0.99    inference(ennf_transformation,[],[f3])).
% 2.50/0.99  
% 2.50/0.99  fof(f24,plain,(
% 2.50/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f11])).
% 2.50/0.99  
% 2.50/0.99  fof(f35,plain,(
% 2.50/0.99    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 2.50/0.99    inference(cnf_transformation,[],[f21])).
% 2.50/0.99  
% 2.50/0.99  fof(f34,plain,(
% 2.50/0.99    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 2.50/0.99    inference(cnf_transformation,[],[f21])).
% 2.50/0.99  
% 2.50/0.99  fof(f33,plain,(
% 2.50/0.99    m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 2.50/0.99    inference(cnf_transformation,[],[f21])).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10,negated_conjecture,
% 2.50/0.99      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1794,plain,
% 2.50/0.99      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4,plain,
% 2.50/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.50/0.99      inference(cnf_transformation,[],[f27]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1800,plain,
% 2.50/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.50/0.99      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2262,plain,
% 2.50/0.99      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1794,c_1800]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2872,plain,
% 2.50/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2262,c_1800]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4868,plain,
% 2.50/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2872,c_1800]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3,plain,
% 2.50/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.50/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1801,plain,
% 2.50/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.50/0.99      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4867,plain,
% 2.50/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2872,c_1801]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_11,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1793,plain,
% 2.50/0.99      ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_5,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.50/0.99      | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
% 2.50/0.99      | k1_xboole_0 = X4
% 2.50/0.99      | k1_xboole_0 = X3
% 2.50/0.99      | k1_xboole_0 = X2
% 2.50/0.99      | k1_xboole_0 = X1 ),
% 2.50/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1799,plain,
% 2.50/0.99      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
% 2.50/0.99      | k1_xboole_0 = X3
% 2.50/0.99      | k1_xboole_0 = X0
% 2.50/0.99      | k1_xboole_0 = X1
% 2.50/0.99      | k1_xboole_0 = X2
% 2.50/0.99      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2561,plain,
% 2.50/0.99      ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
% 2.50/0.99      | sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0 ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1793,c_1799]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_6,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.50/0.99      | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.50/0.99      | k1_xboole_0 = X4
% 2.50/0.99      | k1_xboole_0 = X3
% 2.50/0.99      | k1_xboole_0 = X2
% 2.50/0.99      | k1_xboole_0 = X1 ),
% 2.50/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1798,plain,
% 2.50/0.99      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
% 2.50/0.99      | k1_xboole_0 = X3
% 2.50/0.99      | k1_xboole_0 = X0
% 2.50/0.99      | k1_xboole_0 = X1
% 2.50/0.99      | k1_xboole_0 = X2
% 2.50/0.99      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4619,plain,
% 2.50/0.99      ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
% 2.50/0.99      | sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0 ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1793,c_1798]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_7,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.50/0.99      | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 2.50/0.99      | k1_xboole_0 = X4
% 2.50/0.99      | k1_xboole_0 = X3
% 2.50/0.99      | k1_xboole_0 = X2
% 2.50/0.99      | k1_xboole_0 = X1 ),
% 2.50/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1797,plain,
% 2.50/0.99      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 2.50/0.99      | k1_xboole_0 = X3
% 2.50/0.99      | k1_xboole_0 = X0
% 2.50/0.99      | k1_xboole_0 = X1
% 2.50/0.99      | k1_xboole_0 = X2
% 2.50/0.99      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4196,plain,
% 2.50/0.99      ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 2.50/0.99      | sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0 ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1793,c_1797]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_8,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.50/0.99      | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 2.50/0.99      | k1_xboole_0 = X4
% 2.50/0.99      | k1_xboole_0 = X3
% 2.50/0.99      | k1_xboole_0 = X2
% 2.50/0.99      | k1_xboole_0 = X1 ),
% 2.50/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1796,plain,
% 2.50/0.99      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 2.50/0.99      | k1_xboole_0 = X3
% 2.50/0.99      | k1_xboole_0 = X0
% 2.50/0.99      | k1_xboole_0 = X1
% 2.50/0.99      | k1_xboole_0 = X2
% 2.50/0.99      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2258,plain,
% 2.50/0.99      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
% 2.50/0.99      | sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0 ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1793,c_1796]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_9,negated_conjecture,
% 2.50/0.99      ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
% 2.50/0.99      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
% 2.50/0.99      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
% 2.50/0.99      | ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
% 2.50/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1795,plain,
% 2.50/0.99      ( r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) != iProver_top
% 2.50/0.99      | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
% 2.50/0.99      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.50/0.99      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4187,plain,
% 2.50/0.99      ( sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
% 2.50/0.99      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.50/0.99      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.50/0.99      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2258,c_1795]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_21,plain,
% 2.50/0.99      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1926,plain,
% 2.50/0.99      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
% 2.50/0.99      | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1927,plain,
% 2.50/0.99      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
% 2.50/0.99      | r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1926]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1988,plain,
% 2.50/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
% 2.50/0.99      | ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1992,plain,
% 2.50/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 2.50/0.99      | r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1988]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2179,plain,
% 2.50/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
% 2.50/0.99      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2183,plain,
% 2.50/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) = iProver_top
% 2.50/0.99      | r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2179]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_5480,plain,
% 2.50/0.99      ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.50/0.99      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.50/0.99      | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK3 = k1_xboole_0 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_4187,c_21,c_1927,c_1992,c_2183]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_5481,plain,
% 2.50/0.99      ( sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) != iProver_top
% 2.50/0.99      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.50/0.99      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_5480]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_5491,plain,
% 2.50/0.99      ( sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.50/0.99      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.50/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_4196,c_5481]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2180,plain,
% 2.50/0.99      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
% 2.50/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2181,plain,
% 2.50/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 2.50/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2180]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_7474,plain,
% 2.50/0.99      ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.50/0.99      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK3 = k1_xboole_0 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_5491,c_21,c_1927,c_1992,c_2181]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_7475,plain,
% 2.50/0.99      ( sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) != iProver_top
% 2.50/0.99      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_7474]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_7484,plain,
% 2.50/0.99      ( sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.50/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_4619,c_7475]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1989,plain,
% 2.50/0.99      ( ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
% 2.50/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1990,plain,
% 2.50/0.99      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top
% 2.50/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1989]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_7487,plain,
% 2.50/0.99      ( r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK3 = k1_xboole_0 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_7484,c_21,c_1927,c_1990]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_7488,plain,
% 2.50/0.99      ( sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) != iProver_top ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_7487]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_7496,plain,
% 2.50/0.99      ( sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | r2_hidden(k2_mcart_1(sK8),sK7) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2561,c_7488]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1919,plain,
% 2.50/0.99      ( r2_hidden(k2_mcart_1(sK8),sK7)
% 2.50/0.99      | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_7497,plain,
% 2.50/0.99      ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
% 2.50/0.99      | sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0 ),
% 2.50/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_7496]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_9518,plain,
% 2.50/0.99      ( sK0 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK3 = k1_xboole_0 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_7496,c_21,c_1920]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_9519,plain,
% 2.50/0.99      ( sK3 = k1_xboole_0
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0 ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_9518]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_9530,plain,
% 2.50/0.99      ( sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_9519,c_1793]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2370,plain,
% 2.50/0.99      ( r2_hidden(k2_mcart_1(sK8),sK7) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1794,c_1801]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_12,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1792,plain,
% 2.50/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.50/0.99      | ~ r2_hidden(X2,X0)
% 2.50/0.99      | r2_hidden(X2,X1) ),
% 2.50/0.99      inference(cnf_transformation,[],[f23]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1802,plain,
% 2.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.50/0.99      | r2_hidden(X2,X0) != iProver_top
% 2.50/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2376,plain,
% 2.50/0.99      ( r2_hidden(X0,sK7) != iProver_top | r2_hidden(X0,sK3) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1792,c_1802]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2882,plain,
% 2.50/0.99      ( r2_hidden(k2_mcart_1(sK8),sK3) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2370,c_2376]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_9524,plain,
% 2.50/0.99      ( sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | r2_hidden(k2_mcart_1(sK8),k1_xboole_0) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_9519,c_2882]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_9570,plain,
% 2.50/0.99      ( r2_hidden(k2_mcart_1(sK8),k1_xboole_0)
% 2.50/0.99      | sK2 = k1_xboole_0
% 2.50/0.99      | sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0 ),
% 2.50/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_9524]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_0,plain,
% 2.50/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f22]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2,plain,
% 2.50/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f24]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_177,plain,
% 2.50/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_2]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_178,plain,
% 2.50/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_177]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_9681,plain,
% 2.50/0.99      ( ~ r2_hidden(k2_mcart_1(sK8),k1_xboole_0) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_178]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_9751,plain,
% 2.50/0.99      ( sK0 = k1_xboole_0 | sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_9530,c_12,c_10,c_1547,c_1919,c_2208,c_3325,c_9519,c_9645,
% 2.50/0.99                 c_9643,c_9681]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_9752,plain,
% 2.50/0.99      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_9751]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2871,plain,
% 2.50/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2262,c_1801]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_13,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1791,plain,
% 2.50/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2377,plain,
% 2.50/0.99      ( r2_hidden(X0,sK6) != iProver_top | r2_hidden(X0,sK2) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1791,c_1802]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4622,plain,
% 2.50/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK2) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2871,c_2377]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_9756,plain,
% 2.50/0.99      ( sK1 = k1_xboole_0
% 2.50/0.99      | sK0 = k1_xboole_0
% 2.50/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),k1_xboole_0) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_9752,c_4622]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1788,plain,
% 2.50/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_178]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10036,plain,
% 2.50/0.99      ( sK1 = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 2.50/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_9756,c_1788]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_14,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1790,plain,
% 2.50/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10044,plain,
% 2.50/0.99      ( sK0 = k1_xboole_0
% 2.50/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_10036,c_1790]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10095,plain,
% 2.50/0.99      ( sK0 = k1_xboole_0
% 2.50/0.99      | r2_hidden(X0,sK5) != iProver_top
% 2.50/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_10044,c_1802]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_179,plain,
% 2.50/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_178]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10109,plain,
% 2.50/0.99      ( r2_hidden(X0,sK5) != iProver_top | sK0 = k1_xboole_0 ),
% 2.50/0.99      inference(global_propositional_subsumption,[status(thm)],[c_10095,c_179]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10110,plain,
% 2.50/0.99      ( sK0 = k1_xboole_0 | r2_hidden(X0,sK5) != iProver_top ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_10109]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10117,plain,
% 2.50/0.99      ( sK0 = k1_xboole_0 ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_4867,c_10110]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_15,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1789,plain,
% 2.50/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2379,plain,
% 2.50/0.99      ( r2_hidden(X0,sK4) != iProver_top | r2_hidden(X0,sK0) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1789,c_1802]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10124,plain,
% 2.50/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.50/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.50/0.99      inference(demodulation,[status(thm)],[c_10117,c_2379]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10364,plain,
% 2.50/0.99      ( r2_hidden(X0,sK4) != iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,[status(thm)],[c_10124,c_179]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_10371,plain,
% 2.50/0.99      ( $false ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_4868,c_10364]) ).
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  ------                               Statistics
% 2.50/0.99  
% 2.50/0.99  ------ General
% 2.50/0.99  
% 2.50/0.99  abstr_ref_over_cycles:                  0
% 2.50/0.99  abstr_ref_under_cycles:                 0
% 2.50/0.99  gc_basic_clause_elim:                   0
% 2.50/0.99  forced_gc_time:                         0
% 2.50/0.99  parsing_time:                           0.028
% 2.50/0.99  unif_index_cands_time:                  0.
% 2.50/0.99  unif_index_add_time:                    0.
% 2.50/0.99  orderings_time:                         0.
% 2.50/0.99  out_proof_time:                         0.014
% 2.50/0.99  total_time:                             0.368
% 2.50/0.99  num_of_symbols:                         52
% 2.50/0.99  num_of_terms:                           16170
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing
% 2.50/0.99  
% 2.50/0.99  num_of_splits:                          0
% 2.50/0.99  num_of_split_atoms:                     0
% 2.50/0.99  num_of_reused_defs:                     0
% 2.50/0.99  num_eq_ax_congr_red:                    1
% 2.50/0.99  num_of_sem_filtered_clauses:            1
% 2.50/0.99  num_of_subtypes:                        0
% 2.50/0.99  monotx_restored_types:                  0
% 2.50/0.99  sat_num_of_epr_types:                   0
% 2.50/0.99  sat_num_of_non_cyclic_types:            0
% 2.50/0.99  sat_guarded_non_collapsed_types:        0
% 2.50/0.99  num_pure_diseq_elim:                    0
% 2.50/0.99  simp_replaced_by:                       0
% 2.50/0.99  res_preprocessed:                       86
% 2.50/0.99  prep_upred:                             0
% 2.50/0.99  prep_unflattend:                        52
% 2.50/0.99  smt_new_axioms:                         0
% 2.50/0.99  pred_elim_cands:                        2
% 2.50/0.99  pred_elim:                              1
% 2.50/0.99  pred_elim_cl:                           1
% 2.50/0.99  pred_elim_cycles:                       3
% 2.50/0.99  merged_defs:                            0
% 2.50/0.99  merged_defs_ncl:                        0
% 2.50/0.99  bin_hyper_res:                          0
% 2.50/0.99  prep_cycles:                            4
% 2.50/0.99  pred_elim_time:                         0.033
% 2.50/0.99  splitting_time:                         0.
% 2.50/0.99  sem_filter_time:                        0.
% 2.50/0.99  monotx_time:                            0.001
% 2.50/0.99  subtype_inf_time:                       0.
% 2.50/0.99  
% 2.50/0.99  ------ Problem properties
% 2.50/0.99  
% 2.50/0.99  clauses:                                15
% 2.50/0.99  conjectures:                            7
% 2.50/0.99  epr:                                    1
% 2.50/0.99  horn:                                   11
% 2.50/0.99  ground:                                 7
% 2.50/0.99  unary:                                  7
% 2.50/0.99  binary:                                 2
% 2.50/0.99  lits:                                   42
% 2.50/0.99  lits_eq:                                20
% 2.50/0.99  fd_pure:                                0
% 2.50/0.99  fd_pseudo:                              0
% 2.50/0.99  fd_cond:                                4
% 2.50/0.99  fd_pseudo_cond:                         0
% 2.50/0.99  ac_symbols:                             0
% 2.50/0.99  
% 2.50/0.99  ------ Propositional Solver
% 2.50/0.99  
% 2.50/0.99  prop_solver_calls:                      29
% 2.50/0.99  prop_fast_solver_calls:                 973
% 2.50/0.99  smt_solver_calls:                       0
% 2.50/0.99  smt_fast_solver_calls:                  0
% 2.50/0.99  prop_num_of_clauses:                    3032
% 2.50/0.99  prop_preprocess_simplified:             11655
% 2.50/0.99  prop_fo_subsumed:                       7
% 2.50/0.99  prop_solver_time:                       0.
% 2.50/0.99  smt_solver_time:                        0.
% 2.50/0.99  smt_fast_solver_time:                   0.
% 2.50/0.99  prop_fast_solver_time:                  0.
% 2.50/0.99  prop_unsat_core_time:                   0.
% 2.50/0.99  
% 2.50/0.99  ------ QBF
% 2.50/0.99  
% 2.50/0.99  qbf_q_res:                              0
% 2.50/0.99  qbf_num_tautologies:                    0
% 2.50/0.99  qbf_prep_cycles:                        0
% 2.50/0.99  
% 2.50/0.99  ------ BMC1
% 2.50/0.99  
% 2.50/0.99  bmc1_current_bound:                     -1
% 2.50/0.99  bmc1_last_solved_bound:                 -1
% 2.50/0.99  bmc1_unsat_core_size:                   -1
% 2.50/0.99  bmc1_unsat_core_parents_size:           -1
% 2.50/0.99  bmc1_merge_next_fun:                    0
% 2.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.50/0.99  
% 2.50/0.99  ------ Instantiation
% 2.50/0.99  
% 2.50/0.99  inst_num_of_clauses:                    1193
% 2.50/0.99  inst_num_in_passive:                    713
% 2.50/0.99  inst_num_in_active:                     251
% 2.50/0.99  inst_num_in_unprocessed:                229
% 2.50/0.99  inst_num_of_loops:                      260
% 2.50/0.99  inst_num_of_learning_restarts:          0
% 2.50/0.99  inst_num_moves_active_passive:          8
% 2.50/0.99  inst_lit_activity:                      0
% 2.50/0.99  inst_lit_activity_moves:                0
% 2.50/0.99  inst_num_tautologies:                   0
% 2.50/0.99  inst_num_prop_implied:                  0
% 2.50/0.99  inst_num_existing_simplified:           0
% 2.50/0.99  inst_num_eq_res_simplified:             0
% 2.50/0.99  inst_num_child_elim:                    0
% 2.50/0.99  inst_num_of_dismatching_blockings:      28
% 2.50/0.99  inst_num_of_non_proper_insts:           729
% 2.50/0.99  inst_num_of_duplicates:                 0
% 2.50/0.99  inst_inst_num_from_inst_to_res:         0
% 2.50/0.99  inst_dismatching_checking_time:         0.
% 2.50/0.99  
% 2.50/0.99  ------ Resolution
% 2.50/0.99  
% 2.50/0.99  res_num_of_clauses:                     0
% 2.50/0.99  res_num_in_passive:                     0
% 2.50/0.99  res_num_in_active:                      0
% 2.50/0.99  res_num_of_loops:                       90
% 2.50/0.99  res_forward_subset_subsumed:            24
% 2.50/0.99  res_backward_subset_subsumed:           0
% 2.50/0.99  res_forward_subsumed:                   0
% 2.50/0.99  res_backward_subsumed:                  0
% 2.50/0.99  res_forward_subsumption_resolution:     0
% 2.50/0.99  res_backward_subsumption_resolution:    0
% 2.50/0.99  res_clause_to_clause_subsumption:       43
% 2.50/0.99  res_orphan_elimination:                 0
% 2.50/0.99  res_tautology_del:                      24
% 2.50/0.99  res_num_eq_res_simplified:              0
% 2.50/0.99  res_num_sel_changes:                    0
% 2.50/0.99  res_moves_from_active_to_pass:          0
% 2.50/0.99  
% 2.50/0.99  ------ Superposition
% 2.50/0.99  
% 2.50/0.99  sup_time_total:                         0.
% 2.50/0.99  sup_time_generating:                    0.
% 2.50/0.99  sup_time_sim_full:                      0.
% 2.50/0.99  sup_time_sim_immed:                     0.
% 2.50/0.99  
% 2.50/0.99  sup_num_of_clauses:                     33
% 2.50/0.99  sup_num_in_active:                      32
% 2.50/0.99  sup_num_in_passive:                     1
% 2.50/0.99  sup_num_of_loops:                       51
% 2.50/0.99  sup_fw_superposition:                   31
% 2.50/0.99  sup_bw_superposition:                   48
% 2.50/0.99  sup_immediate_simplified:               27
% 2.50/0.99  sup_given_eliminated:                   0
% 2.50/0.99  comparisons_done:                       0
% 2.50/0.99  comparisons_avoided:                    60
% 2.50/0.99  
% 2.50/0.99  ------ Simplifications
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  sim_fw_subset_subsumed:                 26
% 2.50/0.99  sim_bw_subset_subsumed:                 19
% 2.50/0.99  sim_fw_subsumed:                        0
% 2.50/0.99  sim_bw_subsumed:                        0
% 2.50/0.99  sim_fw_subsumption_res:                 1
% 2.50/0.99  sim_bw_subsumption_res:                 0
% 2.50/0.99  sim_tautology_del:                      0
% 2.50/0.99  sim_eq_tautology_del:                   16
% 2.50/0.99  sim_eq_res_simp:                        0
% 2.50/0.99  sim_fw_demodulated:                     0
% 2.50/0.99  sim_bw_demodulated:                     9
% 2.50/0.99  sim_light_normalised:                   0
% 2.50/0.99  sim_joinable_taut:                      0
% 2.50/0.99  sim_joinable_simp:                      0
% 2.50/0.99  sim_ac_normalised:                      0
% 2.50/0.99  sim_smt_subsumption:                    0
% 2.50/0.99  
%------------------------------------------------------------------------------
