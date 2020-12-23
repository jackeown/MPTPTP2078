%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0927+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:26 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  242 (630891 expanded)
%              Number of clauses        :  159 (179962 expanded)
%              Number of leaves         :   23 (214341 expanded)
%              Depth                    :   60
%              Number of atoms          : 1077 (3864022 expanded)
%              Number of equality atoms :  782 (1123463 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f30])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f29,f38,f37,f36,f35,f34])).

fof(f66,plain,(
    r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ! [X8] :
          ( ! [X9] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
              | X8 != X9
              | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
          | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f57,f40,f40,f40,f40,f40,f40,f40,f40])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( k8_mcart_1(X0,X1,X2,X3,X9) = k8_mcart_1(X4,X5,X6,X7,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f77])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,
    ( ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8)
    | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
    | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
    | ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f55,f40])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f58,f40,f40,f40,f40,f40,f40,f40,f40])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( k9_mcart_1(X0,X1,X2,X3,X9) = k9_mcart_1(X4,X5,X6,X7,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f76])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f40,f40,f40,f40,f40,f40,f40,f40])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( k11_mcart_1(X0,X1,X2,X3,X9) = k11_mcart_1(X4,X5,X6,X7,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f74])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
      | X8 != X9
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f59,f40,f40,f40,f40,f40,f40,f40,f40])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( k10_mcart_1(X0,X1,X2,X3,X9) = k10_mcart_1(X4,X5,X6,X7,X9)
      | ~ m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))
      | ~ m1_subset_1(X9,k4_zfmisc_1(X0,X1,X2,X3))
      | o_0_0_xboole_0 = X7
      | o_0_0_xboole_0 = X6
      | o_0_0_xboole_0 = X5
      | o_0_0_xboole_0 = X4
      | o_0_0_xboole_0 = X3
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f75])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f32])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f50,f40,f40])).

fof(f81,plain,(
    ! [X2,X3,X1] : o_0_0_xboole_0 = k4_zfmisc_1(o_0_0_xboole_0,X1,X2,X3) ),
    inference(equality_resolution,[],[f71])).

fof(f62,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X1
      | o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f51,f40,f40])).

fof(f80,plain,(
    ! [X2,X0,X3] : o_0_0_xboole_0 = k4_zfmisc_1(X0,o_0_0_xboole_0,X2,X3) ),
    inference(equality_resolution,[],[f70])).

fof(f63,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X2
      | o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f52,f40,f40])).

fof(f79,plain,(
    ! [X0,X3,X1] : o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,o_0_0_xboole_0,X3) ),
    inference(equality_resolution,[],[f69])).

fof(f64,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( o_0_0_xboole_0 != X3
      | o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f53,f40,f40])).

fof(f78,plain,(
    ! [X2,X0,X1] : o_0_0_xboole_0 = k4_zfmisc_1(X0,X1,X2,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_5,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_727,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_725,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2145,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_727,c_725])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_716,plain,
    ( r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_726,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1660,plain,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_726])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_715,plain,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X0,k4_zfmisc_1(X5,X6,X7,X8))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k8_mcart_1(X5,X6,X7,X8,X0)
    | o_0_0_xboole_0 = X8
    | o_0_0_xboole_0 = X7
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_718,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k8_mcart_1(X5,X6,X7,X8,X4)
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X8
    | o_0_0_xboole_0 = X7
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X5
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | m1_subset_1(X4,k4_zfmisc_1(X5,X6,X7,X8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2072,plain,
    ( k8_mcart_1(X0,X1,X2,X3,sK9) = k8_mcart_1(sK1,sK2,sK3,sK4,sK9)
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_718])).

cnf(c_5670,plain,
    ( k8_mcart_1(sK5,sK6,sK7,sK8,sK9) = k8_mcart_1(sK1,sK2,sK3,sK4,sK9)
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1660,c_2072])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_730,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5957,plain,
    ( sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) = iProver_top
    | m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5670,c_730])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
    | ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)
    | ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8)
    | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_957,plain,
    ( ~ r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8))
    | m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_328,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1111,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_1125,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_1156,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_1172,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_14,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1301,plain,
    ( ~ v1_xboole_0(sK8)
    | o_0_0_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1334,plain,
    ( ~ v1_xboole_0(sK7)
    | o_0_0_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1517,plain,
    ( ~ v1_xboole_0(sK6)
    | o_0_0_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1591,plain,
    ( ~ v1_xboole_0(sK5)
    | o_0_0_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_329,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1454,plain,
    ( X0 != X1
    | sK8 != X1
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_3257,plain,
    ( X0 != sK8
    | sK8 = X0
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_3258,plain,
    ( sK8 != sK8
    | sK8 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK8 ),
    inference(instantiation,[status(thm)],[c_3257])).

cnf(c_1647,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_3394,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_3395,plain,
    ( sK7 != sK7
    | sK7 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3394])).

cnf(c_1650,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_3405,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_3406,plain,
    ( sK6 != sK6
    | sK6 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_3405])).

cnf(c_1653,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_3416,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_3417,plain,
    ( sK5 != sK5
    | sK5 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3416])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X0,k4_zfmisc_1(X5,X6,X7,X8))
    | k9_mcart_1(X1,X2,X3,X4,X0) = k9_mcart_1(X5,X6,X7,X8,X0)
    | o_0_0_xboole_0 = X8
    | o_0_0_xboole_0 = X7
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_719,plain,
    ( k9_mcart_1(X0,X1,X2,X3,X4) = k9_mcart_1(X5,X6,X7,X8,X4)
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X8
    | o_0_0_xboole_0 = X7
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X5
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | m1_subset_1(X4,k4_zfmisc_1(X5,X6,X7,X8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3627,plain,
    ( k9_mcart_1(X0,X1,X2,X3,sK9) = k9_mcart_1(sK1,sK2,sK3,sK4,sK9)
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_719])).

cnf(c_5705,plain,
    ( k9_mcart_1(sK5,sK6,sK7,sK8,sK9) = k9_mcart_1(sK1,sK2,sK3,sK4,sK9)
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1660,c_3627])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_729,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2456,plain,
    ( r2_hidden(k9_mcart_1(X0,X1,X2,X3,X4),X1) = iProver_top
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_725])).

cnf(c_6614,plain,
    ( sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) = iProver_top
    | m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5705,c_2456])).

cnf(c_6650,plain,
    ( r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
    | ~ m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8))
    | v1_xboole_0(sK6)
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6614])).

cnf(c_2501,plain,
    ( r2_hidden(k8_mcart_1(X0,X1,X2,X3,X4),X0) = iProver_top
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_725])).

cnf(c_7282,plain,
    ( sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) = iProver_top
    | m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5670,c_2501])).

cnf(c_7318,plain,
    ( r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)
    | ~ m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8))
    | v1_xboole_0(sK5)
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7282])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X0,k4_zfmisc_1(X5,X6,X7,X8))
    | k11_mcart_1(X1,X2,X3,X4,X0) = k11_mcart_1(X5,X6,X7,X8,X0)
    | o_0_0_xboole_0 = X8
    | o_0_0_xboole_0 = X7
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_721,plain,
    ( k11_mcart_1(X0,X1,X2,X3,X4) = k11_mcart_1(X5,X6,X7,X8,X4)
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X8
    | o_0_0_xboole_0 = X7
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X5
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | m1_subset_1(X4,k4_zfmisc_1(X5,X6,X7,X8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4889,plain,
    ( k11_mcart_1(X0,X1,X2,X3,sK9) = k11_mcart_1(sK1,sK2,sK3,sK4,sK9)
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_721])).

cnf(c_5871,plain,
    ( k11_mcart_1(sK5,sK6,sK7,sK8,sK9) = k11_mcart_1(sK1,sK2,sK3,sK4,sK9)
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1660,c_4889])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_731,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3747,plain,
    ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X4),X3) = iProver_top
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | v1_xboole_0(X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_725])).

cnf(c_9197,plain,
    ( sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) = iProver_top
    | m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_5871,c_3747])).

cnf(c_9241,plain,
    ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8)
    | ~ m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8))
    | v1_xboole_0(sK8)
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9197])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X0,k4_zfmisc_1(X5,X6,X7,X8))
    | k10_mcart_1(X1,X2,X3,X4,X0) = k10_mcart_1(X5,X6,X7,X8,X0)
    | o_0_0_xboole_0 = X8
    | o_0_0_xboole_0 = X7
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X5
    | o_0_0_xboole_0 = X4
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_720,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = k10_mcart_1(X5,X6,X7,X8,X4)
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X8
    | o_0_0_xboole_0 = X7
    | o_0_0_xboole_0 = X6
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X5
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | m1_subset_1(X4,k4_zfmisc_1(X5,X6,X7,X8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4429,plain,
    ( k10_mcart_1(X0,X1,X2,X3,sK9) = k10_mcart_1(sK1,sK2,sK3,sK4,sK9)
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | o_0_0_xboole_0 = X3
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_720])).

cnf(c_5836,plain,
    ( k10_mcart_1(sK5,sK6,sK7,sK8,sK9) = k10_mcart_1(sK1,sK2,sK3,sK4,sK9)
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1660,c_4429])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4))
    | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_732,plain,
    ( m1_subset_1(X0,k4_zfmisc_1(X1,X2,X3,X4)) != iProver_top
    | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4348,plain,
    ( r2_hidden(k10_mcart_1(X0,X1,X2,X3,X4),X2) = iProver_top
    | m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_732,c_725])).

cnf(c_9382,plain,
    ( sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) = iProver_top
    | m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5836,c_4348])).

cnf(c_9418,plain,
    ( r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
    | ~ m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8))
    | v1_xboole_0(sK7)
    | sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9382])).

cnf(c_9682,plain,
    ( sK5 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5957,c_21,c_20,c_957,c_1111,c_1125,c_1156,c_1172,c_1301,c_1334,c_1517,c_1591,c_3258,c_3395,c_3406,c_3417,c_6650,c_7318,c_9241,c_9418])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_711,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9701,plain,
    ( sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9682,c_711])).

cnf(c_4,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_722,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1540,plain,
    ( v1_xboole_0(k4_zfmisc_1(sK5,sK6,sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_722])).

cnf(c_9699,plain,
    ( sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(k4_zfmisc_1(o_0_0_xboole_0,sK6,sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9682,c_1540])).

cnf(c_11,plain,
    ( k4_zfmisc_1(o_0_0_xboole_0,X0,X1,X2) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_9743,plain,
    ( sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9699,c_11])).

cnf(c_9809,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9743])).

cnf(c_9812,plain,
    ( sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9701,c_64,c_9743])).

cnf(c_9813,plain,
    ( sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_9812])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_712,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9831,plain,
    ( sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9813,c_712])).

cnf(c_64,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9828,plain,
    ( sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(k4_zfmisc_1(sK5,o_0_0_xboole_0,sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9813,c_1540])).

cnf(c_10,plain,
    ( k4_zfmisc_1(X0,o_0_0_xboole_0,X1,X2) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_9888,plain,
    ( sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9828,c_10])).

cnf(c_9959,plain,
    ( sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9831,c_64,c_9888])).

cnf(c_9960,plain,
    ( sK7 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_9959])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_713,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9976,plain,
    ( sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9960,c_713])).

cnf(c_9974,plain,
    ( sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(k4_zfmisc_1(sK5,sK6,o_0_0_xboole_0,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9960,c_1540])).

cnf(c_9,plain,
    ( k4_zfmisc_1(X0,X1,o_0_0_xboole_0,X2) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_10008,plain,
    ( sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9974,c_9])).

cnf(c_10063,plain,
    ( sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK8 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9976,c_64,c_10008])).

cnf(c_10064,plain,
    ( sK8 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_10063])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_714,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10079,plain,
    ( sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10064,c_714])).

cnf(c_10077,plain,
    ( sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(k4_zfmisc_1(sK5,sK6,sK7,o_0_0_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10064,c_1540])).

cnf(c_8,plain,
    ( k4_zfmisc_1(X0,X1,X2,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_10106,plain,
    ( sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10077,c_8])).

cnf(c_10163,plain,
    ( sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK4 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10079,c_64,c_10106])).

cnf(c_10164,plain,
    ( sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_10163])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_724,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1940,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_724])).

cnf(c_6578,plain,
    ( v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2145,c_1940])).

cnf(c_10169,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10164,c_6578])).

cnf(c_10412,plain,
    ( v1_xboole_0(sK8) = iProver_top
    | sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10169,c_64])).

cnf(c_10413,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_10412])).

cnf(c_723,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10421,plain,
    ( sK8 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_10413,c_723])).

cnf(c_10174,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10164,c_714])).

cnf(c_10250,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10174,c_724])).

cnf(c_10488,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10250,c_64])).

cnf(c_10489,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_10488])).

cnf(c_10613,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10421,c_10489])).

cnf(c_10626,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,o_0_0_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10421,c_716])).

cnf(c_10640,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(sK9,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10626,c_8])).

cnf(c_10715,plain,
    ( sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10613,c_10640])).

cnf(c_10736,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10715,c_713])).

cnf(c_10806,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10736,c_724])).

cnf(c_10898,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10806,c_64])).

cnf(c_10899,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_10898])).

cnf(c_10907,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2145,c_10899])).

cnf(c_11067,plain,
    ( sK7 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_10907,c_723])).

cnf(c_11100,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11067,c_10899])).

cnf(c_11112,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,o_0_0_xboole_0,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11067,c_716])).

cnf(c_11123,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | r2_hidden(sK9,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11112,c_9])).

cnf(c_11182,plain,
    ( sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11100,c_11123])).

cnf(c_11223,plain,
    ( sK1 = o_0_0_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11182,c_712])).

cnf(c_11318,plain,
    ( sK1 = o_0_0_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11223,c_724])).

cnf(c_11336,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | sK1 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11318,c_64])).

cnf(c_11337,plain,
    ( sK1 = o_0_0_xboole_0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_11336])).

cnf(c_11344,plain,
    ( sK1 = o_0_0_xboole_0
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2145,c_11337])).

cnf(c_11447,plain,
    ( sK6 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_11344,c_723])).

cnf(c_11516,plain,
    ( sK1 = o_0_0_xboole_0
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11447,c_11337])).

cnf(c_11527,plain,
    ( sK1 = o_0_0_xboole_0
    | r2_hidden(sK9,k4_zfmisc_1(sK5,o_0_0_xboole_0,sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11447,c_716])).

cnf(c_11535,plain,
    ( sK1 = o_0_0_xboole_0
    | r2_hidden(sK9,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11527,c_10])).

cnf(c_11576,plain,
    ( sK1 = o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11516,c_11535])).

cnf(c_1943,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_711,c_724])).

cnf(c_11594,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11576,c_1943])).

cnf(c_12213,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11594,c_64])).

cnf(c_12220,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2145,c_12213])).

cnf(c_12716,plain,
    ( sK5 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_12220,c_723])).

cnf(c_13242,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12716,c_12213])).

cnf(c_13251,plain,
    ( r2_hidden(sK9,k4_zfmisc_1(o_0_0_xboole_0,sK6,sK7,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12716,c_716])).

cnf(c_13253,plain,
    ( r2_hidden(sK9,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13251,c_11])).

cnf(c_13272,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_13242,c_13253])).


%------------------------------------------------------------------------------
