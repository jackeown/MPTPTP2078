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
% DateTime   : Thu Dec  3 11:59:30 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2651)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f17,f27,f26,f25,f24,f23])).

fof(f48,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f57,plain,(
    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f48,f51])).

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

fof(f15,plain,(
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

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f50,plain,
    ( ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8)
    | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
    | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
    | ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2492,plain,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2498,plain,
    ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4291,plain,
    ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(sK9)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2492,c_2498])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2497,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6448,plain,
    ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(sK9))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2492,c_2497])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2496,plain,
    ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3794,plain,
    ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2492,c_2496])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2495,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2951,plain,
    ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2492,c_2495])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)
    | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
    | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
    | ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2494,plain,
    ( r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) != iProver_top
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3445,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2951,c_2494])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2653,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
    | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2654,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top
    | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2653])).

cnf(c_2708,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
    | ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2712,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2708])).

cnf(c_2835,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2839,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) = iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2835])).

cnf(c_3637,plain,
    ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3445,c_25,c_2654,c_2712,c_2839])).

cnf(c_3638,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_3637])).

cnf(c_4593,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3794,c_3638])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2836,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2837,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2836])).

cnf(c_7698,plain,
    ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4593,c_25,c_2654,c_2712,c_2837])).

cnf(c_7699,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_7698])).

cnf(c_7708,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6448,c_7699])).

cnf(c_2709,plain,
    ( ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2710,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2709])).

cnf(c_8331,plain,
    ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7708,c_25,c_2654,c_2710])).

cnf(c_8332,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_8331])).

cnf(c_8340,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4291,c_8332])).

cnf(c_2650,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK8)
    | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8341,plain,
    ( ~ r2_hidden(k2_mcart_1(sK9),sK8)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8340])).

cnf(c_8343,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8340,c_25,c_2651])).

cnf(c_8344,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8343])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2491,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8357,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8344,c_2491])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_262,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_263,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_3433,plain,
    ( ~ r2_hidden(k2_mcart_1(sK9),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_2493,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2500,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4134,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2493,c_2500])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2501,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2955,plain,
    ( r1_tarski(sK8,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2491,c_2501])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2503,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4250,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2955,c_2503])).

cnf(c_5769,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4134,c_4250])).

cnf(c_8350,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK9),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8344,c_5769])).

cnf(c_8404,plain,
    ( r2_hidden(k2_mcart_1(sK9),k1_xboole_0)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8350])).

cnf(c_9030,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8357,c_3436,c_8350])).

cnf(c_9031,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9030])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2490,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9042,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9031,c_2490])).

cnf(c_2846,plain,
    ( ~ r1_tarski(sK7,X0)
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),X0)
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2847,plain,
    ( r1_tarski(sK7,X0) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),X0) = iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2846])).

cnf(c_2849,plain,
    ( r1_tarski(sK7,k1_xboole_0) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2847])).

cnf(c_3396,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | r1_tarski(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3397,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3396])).

cnf(c_3399,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK7,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3397])).

cnf(c_4511,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_4514,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4511])).

cnf(c_9078,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9042,c_25,c_2654,c_2710,c_2849,c_4514,c_9039])).

cnf(c_9079,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9078])).

cnf(c_2499,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4119,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2493,c_2499])).

cnf(c_4480,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4119,c_2499])).

cnf(c_5185,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4480,c_2500])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2489,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2957,plain,
    ( r1_tarski(sK6,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2489,c_2501])).

cnf(c_4252,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2957,c_2503])).

cnf(c_6937,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5185,c_4252])).

cnf(c_15190,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9079,c_6937])).

cnf(c_3329,plain,
    ( ~ r1_tarski(sK6,X0)
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),X0)
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3331,plain,
    ( ~ r1_tarski(sK6,k1_xboole_0)
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6)
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3329])).

cnf(c_9086,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9079,c_2957])).

cnf(c_9112,plain,
    ( r1_tarski(sK6,k1_xboole_0)
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9086])).

cnf(c_15183,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_15193,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15190,c_14,c_2653,c_2708,c_2836,c_3331,c_9112,c_15183])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2488,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2958,plain,
    ( r1_tarski(sK5,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2488,c_2501])).

cnf(c_15202,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15193,c_2958])).

cnf(c_15154,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_15157,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15154])).

cnf(c_3319,plain,
    ( ~ r1_tarski(sK5,X0)
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),X0)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3320,plain,
    ( r1_tarski(sK5,X0) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),X0) = iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3319])).

cnf(c_3322,plain,
    ( r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3320])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15202,c_15157,c_3322,c_2839,c_2712,c_2654,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:13:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.18/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/1.00  
% 3.18/1.00  ------  iProver source info
% 3.18/1.00  
% 3.18/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.18/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/1.00  git: non_committed_changes: false
% 3.18/1.00  git: last_make_outside_of_git: false
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options
% 3.18/1.00  
% 3.18/1.00  --out_options                           all
% 3.18/1.00  --tptp_safe_out                         true
% 3.18/1.00  --problem_path                          ""
% 3.18/1.00  --include_path                          ""
% 3.18/1.00  --clausifier                            res/vclausify_rel
% 3.18/1.00  --clausifier_options                    --mode clausify
% 3.18/1.00  --stdin                                 false
% 3.18/1.00  --stats_out                             all
% 3.18/1.00  
% 3.18/1.00  ------ General Options
% 3.18/1.00  
% 3.18/1.00  --fof                                   false
% 3.18/1.00  --time_out_real                         305.
% 3.18/1.00  --time_out_virtual                      -1.
% 3.18/1.00  --symbol_type_check                     false
% 3.18/1.00  --clausify_out                          false
% 3.18/1.00  --sig_cnt_out                           false
% 3.18/1.00  --trig_cnt_out                          false
% 3.18/1.00  --trig_cnt_out_tolerance                1.
% 3.18/1.00  --trig_cnt_out_sk_spl                   false
% 3.18/1.00  --abstr_cl_out                          false
% 3.18/1.00  
% 3.18/1.00  ------ Global Options
% 3.18/1.00  
% 3.18/1.00  --schedule                              default
% 3.18/1.00  --add_important_lit                     false
% 3.18/1.00  --prop_solver_per_cl                    1000
% 3.18/1.00  --min_unsat_core                        false
% 3.18/1.00  --soft_assumptions                      false
% 3.18/1.00  --soft_lemma_size                       3
% 3.18/1.00  --prop_impl_unit_size                   0
% 3.18/1.00  --prop_impl_unit                        []
% 3.18/1.00  --share_sel_clauses                     true
% 3.18/1.00  --reset_solvers                         false
% 3.18/1.00  --bc_imp_inh                            [conj_cone]
% 3.18/1.00  --conj_cone_tolerance                   3.
% 3.18/1.00  --extra_neg_conj                        none
% 3.18/1.00  --large_theory_mode                     true
% 3.18/1.00  --prolific_symb_bound                   200
% 3.18/1.00  --lt_threshold                          2000
% 3.18/1.00  --clause_weak_htbl                      true
% 3.18/1.00  --gc_record_bc_elim                     false
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing Options
% 3.18/1.00  
% 3.18/1.00  --preprocessing_flag                    true
% 3.18/1.00  --time_out_prep_mult                    0.1
% 3.18/1.00  --splitting_mode                        input
% 3.18/1.00  --splitting_grd                         true
% 3.18/1.00  --splitting_cvd                         false
% 3.18/1.00  --splitting_cvd_svl                     false
% 3.18/1.00  --splitting_nvd                         32
% 3.18/1.00  --sub_typing                            true
% 3.18/1.00  --prep_gs_sim                           true
% 3.18/1.00  --prep_unflatten                        true
% 3.18/1.00  --prep_res_sim                          true
% 3.18/1.00  --prep_upred                            true
% 3.18/1.00  --prep_sem_filter                       exhaustive
% 3.18/1.00  --prep_sem_filter_out                   false
% 3.18/1.00  --pred_elim                             true
% 3.18/1.00  --res_sim_input                         true
% 3.18/1.00  --eq_ax_congr_red                       true
% 3.18/1.00  --pure_diseq_elim                       true
% 3.18/1.00  --brand_transform                       false
% 3.18/1.00  --non_eq_to_eq                          false
% 3.18/1.00  --prep_def_merge                        true
% 3.18/1.00  --prep_def_merge_prop_impl              false
% 3.18/1.00  --prep_def_merge_mbd                    true
% 3.18/1.00  --prep_def_merge_tr_red                 false
% 3.18/1.00  --prep_def_merge_tr_cl                  false
% 3.18/1.00  --smt_preprocessing                     true
% 3.18/1.00  --smt_ac_axioms                         fast
% 3.18/1.00  --preprocessed_out                      false
% 3.18/1.00  --preprocessed_stats                    false
% 3.18/1.00  
% 3.18/1.00  ------ Abstraction refinement Options
% 3.18/1.00  
% 3.18/1.00  --abstr_ref                             []
% 3.18/1.00  --abstr_ref_prep                        false
% 3.18/1.00  --abstr_ref_until_sat                   false
% 3.18/1.00  --abstr_ref_sig_restrict                funpre
% 3.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.00  --abstr_ref_under                       []
% 3.18/1.00  
% 3.18/1.00  ------ SAT Options
% 3.18/1.00  
% 3.18/1.00  --sat_mode                              false
% 3.18/1.00  --sat_fm_restart_options                ""
% 3.18/1.00  --sat_gr_def                            false
% 3.18/1.00  --sat_epr_types                         true
% 3.18/1.00  --sat_non_cyclic_types                  false
% 3.18/1.00  --sat_finite_models                     false
% 3.18/1.00  --sat_fm_lemmas                         false
% 3.18/1.00  --sat_fm_prep                           false
% 3.18/1.00  --sat_fm_uc_incr                        true
% 3.18/1.00  --sat_out_model                         small
% 3.18/1.00  --sat_out_clauses                       false
% 3.18/1.00  
% 3.18/1.00  ------ QBF Options
% 3.18/1.00  
% 3.18/1.00  --qbf_mode                              false
% 3.18/1.00  --qbf_elim_univ                         false
% 3.18/1.00  --qbf_dom_inst                          none
% 3.18/1.00  --qbf_dom_pre_inst                      false
% 3.18/1.00  --qbf_sk_in                             false
% 3.18/1.00  --qbf_pred_elim                         true
% 3.18/1.00  --qbf_split                             512
% 3.18/1.00  
% 3.18/1.00  ------ BMC1 Options
% 3.18/1.00  
% 3.18/1.00  --bmc1_incremental                      false
% 3.18/1.00  --bmc1_axioms                           reachable_all
% 3.18/1.00  --bmc1_min_bound                        0
% 3.18/1.00  --bmc1_max_bound                        -1
% 3.18/1.00  --bmc1_max_bound_default                -1
% 3.18/1.00  --bmc1_symbol_reachability              true
% 3.18/1.00  --bmc1_property_lemmas                  false
% 3.18/1.00  --bmc1_k_induction                      false
% 3.18/1.00  --bmc1_non_equiv_states                 false
% 3.18/1.00  --bmc1_deadlock                         false
% 3.18/1.00  --bmc1_ucm                              false
% 3.18/1.00  --bmc1_add_unsat_core                   none
% 3.18/1.00  --bmc1_unsat_core_children              false
% 3.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.00  --bmc1_out_stat                         full
% 3.18/1.00  --bmc1_ground_init                      false
% 3.18/1.00  --bmc1_pre_inst_next_state              false
% 3.18/1.00  --bmc1_pre_inst_state                   false
% 3.18/1.00  --bmc1_pre_inst_reach_state             false
% 3.18/1.00  --bmc1_out_unsat_core                   false
% 3.18/1.00  --bmc1_aig_witness_out                  false
% 3.18/1.00  --bmc1_verbose                          false
% 3.18/1.00  --bmc1_dump_clauses_tptp                false
% 3.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.00  --bmc1_dump_file                        -
% 3.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.00  --bmc1_ucm_extend_mode                  1
% 3.18/1.00  --bmc1_ucm_init_mode                    2
% 3.18/1.00  --bmc1_ucm_cone_mode                    none
% 3.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.00  --bmc1_ucm_relax_model                  4
% 3.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.00  --bmc1_ucm_layered_model                none
% 3.18/1.00  --bmc1_ucm_max_lemma_size               10
% 3.18/1.00  
% 3.18/1.00  ------ AIG Options
% 3.18/1.00  
% 3.18/1.00  --aig_mode                              false
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation Options
% 3.18/1.00  
% 3.18/1.00  --instantiation_flag                    true
% 3.18/1.00  --inst_sos_flag                         false
% 3.18/1.00  --inst_sos_phase                        true
% 3.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel_side                     num_symb
% 3.18/1.00  --inst_solver_per_active                1400
% 3.18/1.00  --inst_solver_calls_frac                1.
% 3.18/1.00  --inst_passive_queue_type               priority_queues
% 3.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.00  --inst_passive_queues_freq              [25;2]
% 3.18/1.00  --inst_dismatching                      true
% 3.18/1.00  --inst_eager_unprocessed_to_passive     true
% 3.18/1.00  --inst_prop_sim_given                   true
% 3.18/1.00  --inst_prop_sim_new                     false
% 3.18/1.00  --inst_subs_new                         false
% 3.18/1.00  --inst_eq_res_simp                      false
% 3.18/1.00  --inst_subs_given                       false
% 3.18/1.00  --inst_orphan_elimination               true
% 3.18/1.00  --inst_learning_loop_flag               true
% 3.18/1.00  --inst_learning_start                   3000
% 3.18/1.00  --inst_learning_factor                  2
% 3.18/1.00  --inst_start_prop_sim_after_learn       3
% 3.18/1.00  --inst_sel_renew                        solver
% 3.18/1.00  --inst_lit_activity_flag                true
% 3.18/1.00  --inst_restr_to_given                   false
% 3.18/1.00  --inst_activity_threshold               500
% 3.18/1.00  --inst_out_proof                        true
% 3.18/1.00  
% 3.18/1.00  ------ Resolution Options
% 3.18/1.00  
% 3.18/1.00  --resolution_flag                       true
% 3.18/1.00  --res_lit_sel                           adaptive
% 3.18/1.00  --res_lit_sel_side                      none
% 3.18/1.00  --res_ordering                          kbo
% 3.18/1.00  --res_to_prop_solver                    active
% 3.18/1.00  --res_prop_simpl_new                    false
% 3.18/1.00  --res_prop_simpl_given                  true
% 3.18/1.00  --res_passive_queue_type                priority_queues
% 3.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.00  --res_passive_queues_freq               [15;5]
% 3.18/1.00  --res_forward_subs                      full
% 3.18/1.00  --res_backward_subs                     full
% 3.18/1.00  --res_forward_subs_resolution           true
% 3.18/1.00  --res_backward_subs_resolution          true
% 3.18/1.00  --res_orphan_elimination                true
% 3.18/1.00  --res_time_limit                        2.
% 3.18/1.00  --res_out_proof                         true
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Options
% 3.18/1.00  
% 3.18/1.00  --superposition_flag                    true
% 3.18/1.00  --sup_passive_queue_type                priority_queues
% 3.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.00  --demod_completeness_check              fast
% 3.18/1.00  --demod_use_ground                      true
% 3.18/1.00  --sup_to_prop_solver                    passive
% 3.18/1.00  --sup_prop_simpl_new                    true
% 3.18/1.00  --sup_prop_simpl_given                  true
% 3.18/1.00  --sup_fun_splitting                     false
% 3.18/1.00  --sup_smt_interval                      50000
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Simplification Setup
% 3.18/1.00  
% 3.18/1.00  --sup_indices_passive                   []
% 3.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_full_bw                           [BwDemod]
% 3.18/1.00  --sup_immed_triv                        [TrivRules]
% 3.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_immed_bw_main                     []
% 3.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  
% 3.18/1.00  ------ Combination Options
% 3.18/1.00  
% 3.18/1.00  --comb_res_mult                         3
% 3.18/1.00  --comb_sup_mult                         2
% 3.18/1.00  --comb_inst_mult                        10
% 3.18/1.00  
% 3.18/1.00  ------ Debug Options
% 3.18/1.00  
% 3.18/1.00  --dbg_backtrace                         false
% 3.18/1.00  --dbg_dump_prop_clauses                 false
% 3.18/1.00  --dbg_dump_prop_clauses_file            -
% 3.18/1.00  --dbg_out_stat                          false
% 3.18/1.00  ------ Parsing...
% 3.18/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/1.00  ------ Proving...
% 3.18/1.00  ------ Problem Properties 
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  clauses                                 19
% 3.18/1.00  conjectures                             7
% 3.18/1.00  EPR                                     2
% 3.18/1.00  Horn                                    14
% 3.18/1.00  unary                                   7
% 3.18/1.00  binary                                  6
% 3.18/1.00  lits                                    50
% 3.18/1.00  lits eq                                 20
% 3.18/1.00  fd_pure                                 0
% 3.18/1.00  fd_pseudo                               0
% 3.18/1.00  fd_cond                                 4
% 3.18/1.00  fd_pseudo_cond                          0
% 3.18/1.00  AC symbols                              0
% 3.18/1.00  
% 3.18/1.00  ------ Schedule dynamic 5 is on 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  Current options:
% 3.18/1.00  ------ 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options
% 3.18/1.00  
% 3.18/1.00  --out_options                           all
% 3.18/1.00  --tptp_safe_out                         true
% 3.18/1.00  --problem_path                          ""
% 3.18/1.00  --include_path                          ""
% 3.18/1.00  --clausifier                            res/vclausify_rel
% 3.18/1.00  --clausifier_options                    --mode clausify
% 3.18/1.00  --stdin                                 false
% 3.18/1.00  --stats_out                             all
% 3.18/1.00  
% 3.18/1.00  ------ General Options
% 3.18/1.00  
% 3.18/1.00  --fof                                   false
% 3.18/1.00  --time_out_real                         305.
% 3.18/1.00  --time_out_virtual                      -1.
% 3.18/1.00  --symbol_type_check                     false
% 3.18/1.00  --clausify_out                          false
% 3.18/1.00  --sig_cnt_out                           false
% 3.18/1.00  --trig_cnt_out                          false
% 3.18/1.00  --trig_cnt_out_tolerance                1.
% 3.18/1.00  --trig_cnt_out_sk_spl                   false
% 3.18/1.00  --abstr_cl_out                          false
% 3.18/1.00  
% 3.18/1.00  ------ Global Options
% 3.18/1.00  
% 3.18/1.00  --schedule                              default
% 3.18/1.00  --add_important_lit                     false
% 3.18/1.00  --prop_solver_per_cl                    1000
% 3.18/1.00  --min_unsat_core                        false
% 3.18/1.00  --soft_assumptions                      false
% 3.18/1.00  --soft_lemma_size                       3
% 3.18/1.00  --prop_impl_unit_size                   0
% 3.18/1.00  --prop_impl_unit                        []
% 3.18/1.00  --share_sel_clauses                     true
% 3.18/1.00  --reset_solvers                         false
% 3.18/1.00  --bc_imp_inh                            [conj_cone]
% 3.18/1.00  --conj_cone_tolerance                   3.
% 3.18/1.00  --extra_neg_conj                        none
% 3.18/1.00  --large_theory_mode                     true
% 3.18/1.00  --prolific_symb_bound                   200
% 3.18/1.00  --lt_threshold                          2000
% 3.18/1.00  --clause_weak_htbl                      true
% 3.18/1.00  --gc_record_bc_elim                     false
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing Options
% 3.18/1.00  
% 3.18/1.00  --preprocessing_flag                    true
% 3.18/1.00  --time_out_prep_mult                    0.1
% 3.18/1.00  --splitting_mode                        input
% 3.18/1.00  --splitting_grd                         true
% 3.18/1.00  --splitting_cvd                         false
% 3.18/1.00  --splitting_cvd_svl                     false
% 3.18/1.00  --splitting_nvd                         32
% 3.18/1.00  --sub_typing                            true
% 3.18/1.00  --prep_gs_sim                           true
% 3.18/1.00  --prep_unflatten                        true
% 3.18/1.00  --prep_res_sim                          true
% 3.18/1.00  --prep_upred                            true
% 3.18/1.00  --prep_sem_filter                       exhaustive
% 3.18/1.00  --prep_sem_filter_out                   false
% 3.18/1.00  --pred_elim                             true
% 3.18/1.00  --res_sim_input                         true
% 3.18/1.00  --eq_ax_congr_red                       true
% 3.18/1.00  --pure_diseq_elim                       true
% 3.18/1.00  --brand_transform                       false
% 3.18/1.00  --non_eq_to_eq                          false
% 3.18/1.00  --prep_def_merge                        true
% 3.18/1.00  --prep_def_merge_prop_impl              false
% 3.18/1.00  --prep_def_merge_mbd                    true
% 3.18/1.00  --prep_def_merge_tr_red                 false
% 3.18/1.00  --prep_def_merge_tr_cl                  false
% 3.18/1.00  --smt_preprocessing                     true
% 3.18/1.00  --smt_ac_axioms                         fast
% 3.18/1.00  --preprocessed_out                      false
% 3.18/1.00  --preprocessed_stats                    false
% 3.18/1.00  
% 3.18/1.00  ------ Abstraction refinement Options
% 3.18/1.00  
% 3.18/1.00  --abstr_ref                             []
% 3.18/1.00  --abstr_ref_prep                        false
% 3.18/1.00  --abstr_ref_until_sat                   false
% 3.18/1.00  --abstr_ref_sig_restrict                funpre
% 3.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.00  --abstr_ref_under                       []
% 3.18/1.00  
% 3.18/1.00  ------ SAT Options
% 3.18/1.00  
% 3.18/1.00  --sat_mode                              false
% 3.18/1.00  --sat_fm_restart_options                ""
% 3.18/1.00  --sat_gr_def                            false
% 3.18/1.00  --sat_epr_types                         true
% 3.18/1.00  --sat_non_cyclic_types                  false
% 3.18/1.00  --sat_finite_models                     false
% 3.18/1.00  --sat_fm_lemmas                         false
% 3.18/1.00  --sat_fm_prep                           false
% 3.18/1.00  --sat_fm_uc_incr                        true
% 3.18/1.00  --sat_out_model                         small
% 3.18/1.00  --sat_out_clauses                       false
% 3.18/1.00  
% 3.18/1.00  ------ QBF Options
% 3.18/1.00  
% 3.18/1.00  --qbf_mode                              false
% 3.18/1.00  --qbf_elim_univ                         false
% 3.18/1.00  --qbf_dom_inst                          none
% 3.18/1.00  --qbf_dom_pre_inst                      false
% 3.18/1.00  --qbf_sk_in                             false
% 3.18/1.00  --qbf_pred_elim                         true
% 3.18/1.00  --qbf_split                             512
% 3.18/1.00  
% 3.18/1.00  ------ BMC1 Options
% 3.18/1.00  
% 3.18/1.00  --bmc1_incremental                      false
% 3.18/1.00  --bmc1_axioms                           reachable_all
% 3.18/1.00  --bmc1_min_bound                        0
% 3.18/1.00  --bmc1_max_bound                        -1
% 3.18/1.00  --bmc1_max_bound_default                -1
% 3.18/1.00  --bmc1_symbol_reachability              true
% 3.18/1.00  --bmc1_property_lemmas                  false
% 3.18/1.00  --bmc1_k_induction                      false
% 3.18/1.00  --bmc1_non_equiv_states                 false
% 3.18/1.00  --bmc1_deadlock                         false
% 3.18/1.00  --bmc1_ucm                              false
% 3.18/1.00  --bmc1_add_unsat_core                   none
% 3.18/1.00  --bmc1_unsat_core_children              false
% 3.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.00  --bmc1_out_stat                         full
% 3.18/1.00  --bmc1_ground_init                      false
% 3.18/1.00  --bmc1_pre_inst_next_state              false
% 3.18/1.00  --bmc1_pre_inst_state                   false
% 3.18/1.00  --bmc1_pre_inst_reach_state             false
% 3.18/1.00  --bmc1_out_unsat_core                   false
% 3.18/1.00  --bmc1_aig_witness_out                  false
% 3.18/1.00  --bmc1_verbose                          false
% 3.18/1.00  --bmc1_dump_clauses_tptp                false
% 3.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.00  --bmc1_dump_file                        -
% 3.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.00  --bmc1_ucm_extend_mode                  1
% 3.18/1.00  --bmc1_ucm_init_mode                    2
% 3.18/1.00  --bmc1_ucm_cone_mode                    none
% 3.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.00  --bmc1_ucm_relax_model                  4
% 3.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.00  --bmc1_ucm_layered_model                none
% 3.18/1.00  --bmc1_ucm_max_lemma_size               10
% 3.18/1.00  
% 3.18/1.00  ------ AIG Options
% 3.18/1.00  
% 3.18/1.00  --aig_mode                              false
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation Options
% 3.18/1.00  
% 3.18/1.00  --instantiation_flag                    true
% 3.18/1.00  --inst_sos_flag                         false
% 3.18/1.00  --inst_sos_phase                        true
% 3.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel_side                     none
% 3.18/1.00  --inst_solver_per_active                1400
% 3.18/1.00  --inst_solver_calls_frac                1.
% 3.18/1.00  --inst_passive_queue_type               priority_queues
% 3.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.00  --inst_passive_queues_freq              [25;2]
% 3.18/1.00  --inst_dismatching                      true
% 3.18/1.00  --inst_eager_unprocessed_to_passive     true
% 3.18/1.00  --inst_prop_sim_given                   true
% 3.18/1.00  --inst_prop_sim_new                     false
% 3.18/1.00  --inst_subs_new                         false
% 3.18/1.00  --inst_eq_res_simp                      false
% 3.18/1.00  --inst_subs_given                       false
% 3.18/1.00  --inst_orphan_elimination               true
% 3.18/1.00  --inst_learning_loop_flag               true
% 3.18/1.00  --inst_learning_start                   3000
% 3.18/1.00  --inst_learning_factor                  2
% 3.18/1.00  --inst_start_prop_sim_after_learn       3
% 3.18/1.00  --inst_sel_renew                        solver
% 3.18/1.00  --inst_lit_activity_flag                true
% 3.18/1.00  --inst_restr_to_given                   false
% 3.18/1.00  --inst_activity_threshold               500
% 3.18/1.00  --inst_out_proof                        true
% 3.18/1.00  
% 3.18/1.00  ------ Resolution Options
% 3.18/1.00  
% 3.18/1.00  --resolution_flag                       false
% 3.18/1.00  --res_lit_sel                           adaptive
% 3.18/1.00  --res_lit_sel_side                      none
% 3.18/1.00  --res_ordering                          kbo
% 3.18/1.00  --res_to_prop_solver                    active
% 3.18/1.00  --res_prop_simpl_new                    false
% 3.18/1.00  --res_prop_simpl_given                  true
% 3.18/1.00  --res_passive_queue_type                priority_queues
% 3.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.00  --res_passive_queues_freq               [15;5]
% 3.18/1.00  --res_forward_subs                      full
% 3.18/1.00  --res_backward_subs                     full
% 3.18/1.00  --res_forward_subs_resolution           true
% 3.18/1.00  --res_backward_subs_resolution          true
% 3.18/1.00  --res_orphan_elimination                true
% 3.18/1.00  --res_time_limit                        2.
% 3.18/1.00  --res_out_proof                         true
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Options
% 3.18/1.00  
% 3.18/1.00  --superposition_flag                    true
% 3.18/1.00  --sup_passive_queue_type                priority_queues
% 3.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.00  --demod_completeness_check              fast
% 3.18/1.00  --demod_use_ground                      true
% 3.18/1.00  --sup_to_prop_solver                    passive
% 3.18/1.00  --sup_prop_simpl_new                    true
% 3.18/1.00  --sup_prop_simpl_given                  true
% 3.18/1.00  --sup_fun_splitting                     false
% 3.18/1.00  --sup_smt_interval                      50000
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Simplification Setup
% 3.18/1.00  
% 3.18/1.00  --sup_indices_passive                   []
% 3.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_full_bw                           [BwDemod]
% 3.18/1.00  --sup_immed_triv                        [TrivRules]
% 3.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_immed_bw_main                     []
% 3.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  
% 3.18/1.00  ------ Combination Options
% 3.18/1.00  
% 3.18/1.00  --comb_res_mult                         3
% 3.18/1.00  --comb_sup_mult                         2
% 3.18/1.00  --comb_inst_mult                        10
% 3.18/1.00  
% 3.18/1.00  ------ Debug Options
% 3.18/1.00  
% 3.18/1.00  --dbg_backtrace                         false
% 3.18/1.00  --dbg_dump_prop_clauses                 false
% 3.18/1.00  --dbg_dump_prop_clauses_file            -
% 3.18/1.00  --dbg_out_stat                          false
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ Proving...
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS status Theorem for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  fof(f9,conjecture,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f10,negated_conjecture,(
% 3.18/1.00    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 3.18/1.00    inference(negated_conjecture,[],[f9])).
% 3.18/1.00  
% 3.18/1.00  fof(f16,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f10])).
% 3.18/1.00  
% 3.18/1.00  fof(f17,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 3.18/1.00    inference(flattening,[],[f16])).
% 3.18/1.00  
% 3.18/1.00  fof(f27,plain,(
% 3.18/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) => ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,sK9),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,sK9),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,sK9),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,sK9),X4)) & r2_hidden(sK9,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)))) )),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f26,plain,(
% 3.18/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),sK8) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,sK8)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(sK8,k1_zfmisc_1(X3)))) )),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f25,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),sK7) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,sK7,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(sK7,k1_zfmisc_1(X2)))) )),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f24,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),sK6) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,sK6,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(sK6,k1_zfmisc_1(X1)))) )),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f23,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,X8),X7) | ~r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,X8),X6) | ~r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,X8),X5) | ~r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,X8),sK5)) & r2_hidden(X8,k4_zfmisc_1(sK5,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK1,sK2,sK3,sK4))) & m1_subset_1(X7,k1_zfmisc_1(sK4))) & m1_subset_1(X6,k1_zfmisc_1(sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1)))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f28,plain,(
% 3.18/1.00    (((((~r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) | ~r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) | ~r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) | ~r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)) & r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) & m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4))) & m1_subset_1(sK8,k1_zfmisc_1(sK4))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f17,f27,f26,f25,f24,f23])).
% 3.18/1.00  
% 3.18/1.00  fof(f48,plain,(
% 3.18/1.00    m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 3.18/1.00    inference(cnf_transformation,[],[f28])).
% 3.18/1.00  
% 3.18/1.00  fof(f6,axiom,(
% 3.18/1.00    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f37,plain,(
% 3.18/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f6])).
% 3.18/1.00  
% 3.18/1.00  fof(f5,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f36,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f5])).
% 3.18/1.00  
% 3.18/1.00  fof(f51,plain,(
% 3.18/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.18/1.00    inference(definition_unfolding,[],[f37,f36])).
% 3.18/1.00  
% 3.18/1.00  fof(f57,plain,(
% 3.18/1.00    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 3.18/1.00    inference(definition_unfolding,[],[f48,f51])).
% 3.18/1.00  
% 3.18/1.00  fof(f8,axiom,(
% 3.18/1.00    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f15,plain,(
% 3.18/1.00    ! [X0,X1,X2,X3] : (! [X4] : ((k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.18/1.00    inference(ennf_transformation,[],[f8])).
% 3.18/1.00  
% 3.18/1.00  fof(f43,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f15])).
% 3.18/1.00  
% 3.18/1.00  fof(f52,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(definition_unfolding,[],[f43,f51])).
% 3.18/1.00  
% 3.18/1.00  fof(f42,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f15])).
% 3.18/1.00  
% 3.18/1.00  fof(f53,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(definition_unfolding,[],[f42,f51])).
% 3.18/1.00  
% 3.18/1.00  fof(f41,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f15])).
% 3.18/1.00  
% 3.18/1.00  fof(f54,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(definition_unfolding,[],[f41,f51])).
% 3.18/1.00  
% 3.18/1.00  fof(f40,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f15])).
% 3.18/1.00  
% 3.18/1.00  fof(f55,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(definition_unfolding,[],[f40,f51])).
% 3.18/1.00  
% 3.18/1.00  fof(f50,plain,(
% 3.18/1.00    ~r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) | ~r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) | ~r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) | ~r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)),
% 3.18/1.00    inference(cnf_transformation,[],[f28])).
% 3.18/1.00  
% 3.18/1.00  fof(f49,plain,(
% 3.18/1.00    r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8))),
% 3.18/1.00    inference(cnf_transformation,[],[f28])).
% 3.18/1.00  
% 3.18/1.00  fof(f56,plain,(
% 3.18/1.00    r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8))),
% 3.18/1.00    inference(definition_unfolding,[],[f49,f51])).
% 3.18/1.00  
% 3.18/1.00  fof(f7,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f14,plain,(
% 3.18/1.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.18/1.00    inference(ennf_transformation,[],[f7])).
% 3.18/1.00  
% 3.18/1.00  fof(f38,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f14])).
% 3.18/1.00  
% 3.18/1.00  fof(f39,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f14])).
% 3.18/1.00  
% 3.18/1.00  fof(f47,plain,(
% 3.18/1.00    m1_subset_1(sK8,k1_zfmisc_1(sK4))),
% 3.18/1.00    inference(cnf_transformation,[],[f28])).
% 3.18/1.00  
% 3.18/1.00  fof(f1,axiom,(
% 3.18/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f11,plain,(
% 3.18/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.18/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.18/1.00  
% 3.18/1.00  fof(f12,plain,(
% 3.18/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.18/1.00    inference(ennf_transformation,[],[f11])).
% 3.18/1.00  
% 3.18/1.00  fof(f29,plain,(
% 3.18/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f12])).
% 3.18/1.00  
% 3.18/1.00  fof(f3,axiom,(
% 3.18/1.00    v1_xboole_0(k1_xboole_0)),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f33,plain,(
% 3.18/1.00    v1_xboole_0(k1_xboole_0)),
% 3.18/1.00    inference(cnf_transformation,[],[f3])).
% 3.18/1.00  
% 3.18/1.00  fof(f4,axiom,(
% 3.18/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f22,plain,(
% 3.18/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.18/1.00    inference(nnf_transformation,[],[f4])).
% 3.18/1.00  
% 3.18/1.00  fof(f34,plain,(
% 3.18/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f22])).
% 3.18/1.00  
% 3.18/1.00  fof(f2,axiom,(
% 3.18/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f13,plain,(
% 3.18/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f2])).
% 3.18/1.00  
% 3.18/1.00  fof(f18,plain,(
% 3.18/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.18/1.00    inference(nnf_transformation,[],[f13])).
% 3.18/1.00  
% 3.18/1.00  fof(f19,plain,(
% 3.18/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.18/1.00    inference(rectify,[],[f18])).
% 3.18/1.00  
% 3.18/1.00  fof(f20,plain,(
% 3.18/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f21,plain,(
% 3.18/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.18/1.00  
% 3.18/1.00  fof(f30,plain,(
% 3.18/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f21])).
% 3.18/1.00  
% 3.18/1.00  fof(f46,plain,(
% 3.18/1.00    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 3.18/1.00    inference(cnf_transformation,[],[f28])).
% 3.18/1.00  
% 3.18/1.00  fof(f45,plain,(
% 3.18/1.00    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 3.18/1.00    inference(cnf_transformation,[],[f28])).
% 3.18/1.00  
% 3.18/1.00  fof(f44,plain,(
% 3.18/1.00    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 3.18/1.00    inference(cnf_transformation,[],[f28])).
% 3.18/1.00  
% 3.18/1.00  cnf(c_15,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2492,plain,
% 3.18/1.00      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.18/1.00      | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
% 3.18/1.00      | k1_xboole_0 = X4
% 3.18/1.00      | k1_xboole_0 = X3
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X1 ),
% 3.18/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2498,plain,
% 3.18/1.00      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
% 3.18/1.00      | k1_xboole_0 = X1
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X0
% 3.18/1.00      | k1_xboole_0 = X3
% 3.18/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4291,plain,
% 3.18/1.00      ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(sK9)
% 3.18/1.00      | sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2492,c_2498]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.18/1.00      | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.18/1.00      | k1_xboole_0 = X4
% 3.18/1.00      | k1_xboole_0 = X3
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X1 ),
% 3.18/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2497,plain,
% 3.18/1.00      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
% 3.18/1.00      | k1_xboole_0 = X1
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X0
% 3.18/1.00      | k1_xboole_0 = X3
% 3.18/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6448,plain,
% 3.18/1.00      ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(sK9))
% 3.18/1.00      | sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2492,c_2497]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_11,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.18/1.00      | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 3.18/1.00      | k1_xboole_0 = X4
% 3.18/1.00      | k1_xboole_0 = X3
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X1 ),
% 3.18/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2496,plain,
% 3.18/1.00      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 3.18/1.00      | k1_xboole_0 = X1
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X0
% 3.18/1.00      | k1_xboole_0 = X3
% 3.18/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3794,plain,
% 3.18/1.00      ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 3.18/1.00      | sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2492,c_2496]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_12,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.18/1.00      | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 3.18/1.00      | k1_xboole_0 = X4
% 3.18/1.00      | k1_xboole_0 = X3
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X1 ),
% 3.18/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2495,plain,
% 3.18/1.00      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 3.18/1.00      | k1_xboole_0 = X1
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X0
% 3.18/1.00      | k1_xboole_0 = X3
% 3.18/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2951,plain,
% 3.18/1.00      ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 3.18/1.00      | sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2492,c_2495]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_13,negated_conjecture,
% 3.18/1.00      ( ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)
% 3.18/1.00      | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
% 3.18/1.00      | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
% 3.18/1.00      | ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) ),
% 3.18/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2494,plain,
% 3.18/1.00      ( r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) != iProver_top
% 3.18/1.00      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 3.18/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.18/1.00      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3445,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 3.18/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.18/1.00      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.18/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2951,c_2494]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_14,negated_conjecture,
% 3.18/1.00      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_25,plain,
% 3.18/1.00      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.18/1.00      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2653,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
% 3.18/1.00      | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2654,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top
% 3.18/1.00      | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2653]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2708,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
% 3.18/1.00      | ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2712,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top
% 3.18/1.00      | r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2708]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2835,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5)
% 3.18/1.00      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2839,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) = iProver_top
% 3.18/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2835]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3637,plain,
% 3.18/1.00      ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.18/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.18/1.00      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK4 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_3445,c_25,c_2654,c_2712,c_2839]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3638,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 3.18/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.18/1.00      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_3637]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4593,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.18/1.00      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3794,c_3638]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.18/1.00      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.18/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2836,plain,
% 3.18/1.00      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2837,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2836]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7698,plain,
% 3.18/1.00      ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.18/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK4 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_4593,c_25,c_2654,c_2712,c_2837]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7699,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 3.18/1.00      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_7698]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7708,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_6448,c_7699]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2709,plain,
% 3.18/1.00      ( ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2710,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2709]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8331,plain,
% 3.18/1.00      ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK4 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_7708,c_25,c_2654,c_2710]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8332,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_8331]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8340,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_4291,c_8332]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2650,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(sK9),sK8)
% 3.18/1.00      | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8341,plain,
% 3.18/1.00      ( ~ r2_hidden(k2_mcart_1(sK9),sK8)
% 3.18/1.00      | sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_8340]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8343,plain,
% 3.18/1.00      ( sK1 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK4 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_8340,c_25,c_2651]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8344,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_8343]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_16,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2491,plain,
% 3.18/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8357,plain,
% 3.18/1.00      ( sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_8344,c_2491]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_0,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4,plain,
% 3.18/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_262,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_263,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_262]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3433,plain,
% 3.18/1.00      ( ~ r2_hidden(k2_mcart_1(sK9),k1_xboole_0) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_263]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2493,plain,
% 3.18/1.00      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2500,plain,
% 3.18/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4134,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(sK9),sK8) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2493,c_2500]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2501,plain,
% 3.18/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.18/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2955,plain,
% 3.18/1.00      ( r1_tarski(sK8,sK4) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2491,c_2501]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3,plain,
% 3.18/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2503,plain,
% 3.18/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.18/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.18/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4250,plain,
% 3.18/1.00      ( r2_hidden(X0,sK8) != iProver_top
% 3.18/1.00      | r2_hidden(X0,sK4) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2955,c_2503]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5769,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(sK9),sK4) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_4134,c_4250]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8350,plain,
% 3.18/1.00      ( sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k2_mcart_1(sK9),k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_8344,c_5769]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8404,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(sK9),k1_xboole_0)
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_8350]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9030,plain,
% 3.18/1.00      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_8357,c_3436,c_8350]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9031,plain,
% 3.18/1.00      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_9030]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_17,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2490,plain,
% 3.18/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9042,plain,
% 3.18/1.00      ( sK2 = k1_xboole_0
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_9031,c_2490]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2846,plain,
% 3.18/1.00      ( ~ r1_tarski(sK7,X0)
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),X0)
% 3.18/1.00      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2847,plain,
% 3.18/1.00      ( r1_tarski(sK7,X0) != iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),X0) = iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2846]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2849,plain,
% 3.18/1.00      ( r1_tarski(sK7,k1_xboole_0) != iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_2847]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3396,plain,
% 3.18/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0)) | r1_tarski(sK7,X0) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3397,plain,
% 3.18/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(X0)) != iProver_top
% 3.18/1.00      | r1_tarski(sK7,X0) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3396]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3399,plain,
% 3.18/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.18/1.00      | r1_tarski(sK7,k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_3397]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4511,plain,
% 3.18/1.00      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_263]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4514,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_4511]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9078,plain,
% 3.18/1.00      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_9042,c_25,c_2654,c_2710,c_2849,c_4514,c_9039]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9079,plain,
% 3.18/1.00      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_9078]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2499,plain,
% 3.18/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.18/1.00      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4119,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2493,c_2499]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4480,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_4119,c_2499]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5185,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_4480,c_2500]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_18,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2489,plain,
% 3.18/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2957,plain,
% 3.18/1.00      ( r1_tarski(sK6,sK2) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2489,c_2501]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4252,plain,
% 3.18/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 3.18/1.00      | r2_hidden(X0,sK2) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2957,c_2503]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6937,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK2) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_5185,c_4252]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_15190,plain,
% 3.18/1.00      ( sK1 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_9079,c_6937]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3329,plain,
% 3.18/1.00      ( ~ r1_tarski(sK6,X0)
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),X0)
% 3.18/1.00      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3331,plain,
% 3.18/1.00      ( ~ r1_tarski(sK6,k1_xboole_0)
% 3.18/1.00      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6)
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_3329]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9086,plain,
% 3.18/1.00      ( sK1 = k1_xboole_0 | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_9079,c_2957]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9112,plain,
% 3.18/1.00      ( r1_tarski(sK6,k1_xboole_0) | sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_9086]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_15183,plain,
% 3.18/1.00      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_263]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_15193,plain,
% 3.18/1.00      ( sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_15190,c_14,c_2653,c_2708,c_2836,c_3331,c_9112,c_15183]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_19,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2488,plain,
% 3.18/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2958,plain,
% 3.18/1.00      ( r1_tarski(sK5,sK1) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2488,c_2501]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_15202,plain,
% 3.18/1.00      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_15193,c_2958]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_15154,plain,
% 3.18/1.00      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_263]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_15157,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_15154]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3319,plain,
% 3.18/1.00      ( ~ r1_tarski(sK5,X0)
% 3.18/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),X0)
% 3.18/1.00      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3320,plain,
% 3.18/1.00      ( r1_tarski(sK5,X0) != iProver_top
% 3.18/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),X0) = iProver_top
% 3.18/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3319]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3322,plain,
% 3.18/1.00      ( r1_tarski(sK5,k1_xboole_0) != iProver_top
% 3.18/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) != iProver_top
% 3.18/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_3320]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(contradiction,plain,
% 3.18/1.00      ( $false ),
% 3.18/1.00      inference(minisat,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_15202,c_15157,c_3322,c_2839,c_2712,c_2654,c_25]) ).
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  ------                               Statistics
% 3.18/1.00  
% 3.18/1.00  ------ General
% 3.18/1.00  
% 3.18/1.00  abstr_ref_over_cycles:                  0
% 3.18/1.00  abstr_ref_under_cycles:                 0
% 3.18/1.00  gc_basic_clause_elim:                   0
% 3.18/1.00  forced_gc_time:                         0
% 3.18/1.00  parsing_time:                           0.012
% 3.18/1.00  unif_index_cands_time:                  0.
% 3.18/1.00  unif_index_add_time:                    0.
% 3.18/1.00  orderings_time:                         0.
% 3.18/1.00  out_proof_time:                         0.014
% 3.18/1.00  total_time:                             0.436
% 3.18/1.00  num_of_symbols:                         54
% 3.18/1.00  num_of_terms:                           21610
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing
% 3.18/1.00  
% 3.18/1.00  num_of_splits:                          0
% 3.18/1.00  num_of_split_atoms:                     0
% 3.18/1.00  num_of_reused_defs:                     0
% 3.18/1.00  num_eq_ax_congr_red:                    12
% 3.18/1.00  num_of_sem_filtered_clauses:            1
% 3.18/1.00  num_of_subtypes:                        0
% 3.18/1.00  monotx_restored_types:                  0
% 3.18/1.00  sat_num_of_epr_types:                   0
% 3.18/1.00  sat_num_of_non_cyclic_types:            0
% 3.18/1.00  sat_guarded_non_collapsed_types:        0
% 3.18/1.00  num_pure_diseq_elim:                    0
% 3.18/1.00  simp_replaced_by:                       0
% 3.18/1.00  res_preprocessed:                       102
% 3.18/1.00  prep_upred:                             0
% 3.18/1.00  prep_unflattend:                        59
% 3.18/1.00  smt_new_axioms:                         0
% 3.18/1.00  pred_elim_cands:                        3
% 3.18/1.00  pred_elim:                              1
% 3.18/1.00  pred_elim_cl:                           1
% 3.18/1.00  pred_elim_cycles:                       5
% 3.18/1.00  merged_defs:                            8
% 3.18/1.00  merged_defs_ncl:                        0
% 3.18/1.00  bin_hyper_res:                          8
% 3.18/1.00  prep_cycles:                            4
% 3.18/1.00  pred_elim_time:                         0.031
% 3.18/1.00  splitting_time:                         0.
% 3.18/1.00  sem_filter_time:                        0.
% 3.18/1.00  monotx_time:                            0.
% 3.18/1.00  subtype_inf_time:                       0.
% 3.18/1.00  
% 3.18/1.00  ------ Problem properties
% 3.18/1.00  
% 3.18/1.00  clauses:                                19
% 3.18/1.00  conjectures:                            7
% 3.18/1.00  epr:                                    2
% 3.18/1.00  horn:                                   14
% 3.18/1.00  ground:                                 7
% 3.18/1.00  unary:                                  7
% 3.18/1.00  binary:                                 6
% 3.18/1.00  lits:                                   50
% 3.18/1.00  lits_eq:                                20
% 3.18/1.00  fd_pure:                                0
% 3.18/1.00  fd_pseudo:                              0
% 3.18/1.00  fd_cond:                                4
% 3.18/1.00  fd_pseudo_cond:                         0
% 3.18/1.00  ac_symbols:                             0
% 3.18/1.00  
% 3.18/1.00  ------ Propositional Solver
% 3.18/1.00  
% 3.18/1.00  prop_solver_calls:                      29
% 3.18/1.00  prop_fast_solver_calls:                 1134
% 3.18/1.00  smt_solver_calls:                       0
% 3.18/1.00  smt_fast_solver_calls:                  0
% 3.18/1.00  prop_num_of_clauses:                    5168
% 3.18/1.00  prop_preprocess_simplified:             15435
% 3.18/1.00  prop_fo_subsumed:                       7
% 3.18/1.00  prop_solver_time:                       0.
% 3.18/1.00  smt_solver_time:                        0.
% 3.18/1.00  smt_fast_solver_time:                   0.
% 3.18/1.00  prop_fast_solver_time:                  0.
% 3.18/1.00  prop_unsat_core_time:                   0.
% 3.18/1.00  
% 3.18/1.00  ------ QBF
% 3.18/1.00  
% 3.18/1.00  qbf_q_res:                              0
% 3.18/1.00  qbf_num_tautologies:                    0
% 3.18/1.00  qbf_prep_cycles:                        0
% 3.18/1.00  
% 3.18/1.00  ------ BMC1
% 3.18/1.00  
% 3.18/1.00  bmc1_current_bound:                     -1
% 3.18/1.00  bmc1_last_solved_bound:                 -1
% 3.18/1.00  bmc1_unsat_core_size:                   -1
% 3.18/1.00  bmc1_unsat_core_parents_size:           -1
% 3.18/1.00  bmc1_merge_next_fun:                    0
% 3.18/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation
% 3.18/1.00  
% 3.18/1.00  inst_num_of_clauses:                    1739
% 3.18/1.00  inst_num_in_passive:                    813
% 3.18/1.00  inst_num_in_active:                     314
% 3.18/1.00  inst_num_in_unprocessed:                612
% 3.18/1.00  inst_num_of_loops:                      330
% 3.18/1.00  inst_num_of_learning_restarts:          0
% 3.18/1.00  inst_num_moves_active_passive:          14
% 3.18/1.00  inst_lit_activity:                      0
% 3.18/1.00  inst_lit_activity_moves:                0
% 3.18/1.00  inst_num_tautologies:                   0
% 3.18/1.00  inst_num_prop_implied:                  0
% 3.18/1.00  inst_num_existing_simplified:           0
% 3.18/1.00  inst_num_eq_res_simplified:             0
% 3.18/1.00  inst_num_child_elim:                    0
% 3.18/1.00  inst_num_of_dismatching_blockings:      48
% 3.18/1.00  inst_num_of_non_proper_insts:           1517
% 3.18/1.00  inst_num_of_duplicates:                 0
% 3.18/1.00  inst_inst_num_from_inst_to_res:         0
% 3.18/1.00  inst_dismatching_checking_time:         0.
% 3.18/1.00  
% 3.18/1.00  ------ Resolution
% 3.18/1.00  
% 3.18/1.00  res_num_of_clauses:                     0
% 3.18/1.00  res_num_in_passive:                     0
% 3.18/1.00  res_num_in_active:                      0
% 3.18/1.00  res_num_of_loops:                       106
% 3.18/1.00  res_forward_subset_subsumed:            14
% 3.18/1.00  res_backward_subset_subsumed:           0
% 3.18/1.00  res_forward_subsumed:                   0
% 3.18/1.00  res_backward_subsumed:                  0
% 3.18/1.00  res_forward_subsumption_resolution:     0
% 3.18/1.00  res_backward_subsumption_resolution:    0
% 3.18/1.00  res_clause_to_clause_subsumption:       275
% 3.18/1.00  res_orphan_elimination:                 0
% 3.18/1.00  res_tautology_del:                      43
% 3.18/1.00  res_num_eq_res_simplified:              0
% 3.18/1.00  res_num_sel_changes:                    0
% 3.18/1.00  res_moves_from_active_to_pass:          0
% 3.18/1.00  
% 3.18/1.00  ------ Superposition
% 3.18/1.00  
% 3.18/1.00  sup_time_total:                         0.
% 3.18/1.00  sup_time_generating:                    0.
% 3.18/1.00  sup_time_sim_full:                      0.
% 3.18/1.00  sup_time_sim_immed:                     0.
% 3.18/1.00  
% 3.18/1.00  sup_num_of_clauses:                     82
% 3.18/1.00  sup_num_in_active:                      44
% 3.18/1.00  sup_num_in_passive:                     38
% 3.18/1.00  sup_num_of_loops:                       65
% 3.18/1.00  sup_fw_superposition:                   50
% 3.18/1.00  sup_bw_superposition:                   79
% 3.18/1.00  sup_immediate_simplified:               29
% 3.18/1.00  sup_given_eliminated:                   0
% 3.18/1.00  comparisons_done:                       0
% 3.18/1.00  comparisons_avoided:                    60
% 3.18/1.00  
% 3.18/1.00  ------ Simplifications
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  sim_fw_subset_subsumed:                 29
% 3.18/1.00  sim_bw_subset_subsumed:                 20
% 3.18/1.00  sim_fw_subsumed:                        0
% 3.18/1.00  sim_bw_subsumed:                        0
% 3.18/1.00  sim_fw_subsumption_res:                 1
% 3.18/1.00  sim_bw_subsumption_res:                 0
% 3.18/1.00  sim_tautology_del:                      2
% 3.18/1.00  sim_eq_tautology_del:                   8
% 3.18/1.00  sim_eq_res_simp:                        0
% 3.18/1.00  sim_fw_demodulated:                     0
% 3.18/1.00  sim_bw_demodulated:                     10
% 3.18/1.00  sim_light_normalised:                   0
% 3.18/1.00  sim_joinable_taut:                      0
% 3.18/1.00  sim_joinable_simp:                      0
% 3.18/1.00  sim_ac_normalised:                      0
% 3.18/1.00  sim_smt_subsumption:                    0
% 3.18/1.00  
%------------------------------------------------------------------------------
