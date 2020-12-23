%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:30 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  185 (3066 expanded)
%              Number of clauses        :  118 ( 814 expanded)
%              Number of leaves         :   19 ( 962 expanded)
%              Depth                    :   28
%              Number of atoms          :  625 (17617 expanded)
%              Number of equality atoms :  303 (2722 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ? [X8] :
          ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
            | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
            | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
            | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
          & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
          & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
     => ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,sK11),X7)
          | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,sK11),X6)
          | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,sK11),X5)
          | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,sK11),X4) )
        & r2_hidden(sK11,k4_zfmisc_1(X4,X5,X6,X7))
        & m1_subset_1(sK11,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
            ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),sK10)
              | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
              | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
              | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
            & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,sK10))
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & m1_subset_1(sK10,k1_zfmisc_1(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
                  | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),sK9)
                  | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                  | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                & r2_hidden(X8,k4_zfmisc_1(X4,X5,sK9,X7))
                & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
            & m1_subset_1(X7,k1_zfmisc_1(X3)) )
        & m1_subset_1(sK9,k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
                      | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),sK8)
                      | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                    & r2_hidden(X8,k4_zfmisc_1(X4,sK8,X6,X7))
                    & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                & m1_subset_1(X7,k1_zfmisc_1(X3)) )
            & m1_subset_1(X6,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK8,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
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
                      ( ( ~ r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(sK3,sK4,sK5,sK6,X8),sK7) )
                      & r2_hidden(X8,k4_zfmisc_1(sK7,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(sK3,sK4,sK5,sK6)) )
                  & m1_subset_1(X7,k1_zfmisc_1(sK6)) )
              & m1_subset_1(X6,k1_zfmisc_1(sK5)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK4)) )
      & m1_subset_1(sK7,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ~ r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10)
      | ~ r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9)
      | ~ r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,sK11),sK8)
      | ~ r2_hidden(k8_mcart_1(sK3,sK4,sK5,sK6,sK11),sK7) )
    & r2_hidden(sK11,k4_zfmisc_1(sK7,sK8,sK9,sK10))
    & m1_subset_1(sK11,k4_zfmisc_1(sK3,sK4,sK5,sK6))
    & m1_subset_1(sK10,k1_zfmisc_1(sK6))
    & m1_subset_1(sK9,k1_zfmisc_1(sK5))
    & m1_subset_1(sK8,k1_zfmisc_1(sK4))
    & m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f19,f36,f35,f34,f33,f32])).

fof(f62,plain,(
    m1_subset_1(sK11,k4_zfmisc_1(sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f71,plain,(
    m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6)) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f10,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f64,plain,
    ( ~ r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10)
    | ~ r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9)
    | ~ r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,sK11),sK8)
    | ~ r2_hidden(k8_mcart_1(sK3,sK4,sK5,sK6,sK11),sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    r2_hidden(sK11,k4_zfmisc_1(sK7,sK8,sK9,sK10)) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10)) ),
    inference(definition_unfolding,[],[f63,f65])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(sK6)) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1736,plain,
    ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1742,plain,
    ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3464,plain,
    ( k11_mcart_1(sK3,sK4,sK5,sK6,sK11) = k2_mcart_1(sK11)
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1736,c_1742])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1741,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3369,plain,
    ( k10_mcart_1(sK3,sK4,sK5,sK6,sK11) = k2_mcart_1(k1_mcart_1(sK11))
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1736,c_1741])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1740,plain,
    ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2574,plain,
    ( k9_mcart_1(sK3,sK4,sK5,sK6,sK11) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK11)))
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1736,c_1740])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1739,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2062,plain,
    ( k8_mcart_1(sK3,sK4,sK5,sK6,sK11) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK11)))
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1736,c_1739])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(sK3,sK4,sK5,sK6,sK11),sK7)
    | ~ r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,sK11),sK8)
    | ~ r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9)
    | ~ r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1738,plain,
    ( r2_hidden(k8_mcart_1(sK3,sK4,sK5,sK6,sK11),sK7) != iProver_top
    | r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,sK11),sK8) != iProver_top
    | r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9) != iProver_top
    | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2250,plain,
    ( sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,sK11),sK8) != iProver_top
    | r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9) != iProver_top
    | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK11))),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2062,c_1738])).

cnf(c_3285,plain,
    ( sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9) != iProver_top
    | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK11))),sK7) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK11))),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2574,c_2250])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1737,plain,
    ( r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1743,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2408,plain,
    ( r2_hidden(k1_mcart_1(sK11),k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_1743])).

cnf(c_2415,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK11)),k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2408,c_1743])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1744,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4412,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK11))),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_1744])).

cnf(c_4413,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK11))),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_1743])).

cnf(c_4994,plain,
    ( sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9) != iProver_top
    | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3285,c_4412,c_4413])).

cnf(c_4998,plain,
    ( sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK11)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3369,c_4994])).

cnf(c_2698,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK11)),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_2408,c_1744])).

cnf(c_5001,plain,
    ( r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4998,c_2698])).

cnf(c_5002,plain,
    ( sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_5001])).

cnf(c_5005,plain,
    ( sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK11),sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_3464,c_5002])).

cnf(c_2697,plain,
    ( r2_hidden(k2_mcart_1(sK11),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_1744])).

cnf(c_5110,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5005,c_2697])).

cnf(c_5111,plain,
    ( sK6 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5110])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(sK6)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1735,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1745,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2786,plain,
    ( r2_hidden(sK10,k1_zfmisc_1(sK6)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_1745])).

cnf(c_574,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK6) != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_575,plain,
    ( r2_hidden(sK10,k1_zfmisc_1(sK6))
    | v1_xboole_0(k1_zfmisc_1(sK6)) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_581,plain,
    ( r2_hidden(sK10,k1_zfmisc_1(sK6)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_575,c_10])).

cnf(c_583,plain,
    ( r2_hidden(sK10,k1_zfmisc_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_2923,plain,
    ( r2_hidden(sK10,k1_zfmisc_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2786,c_583])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1747,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2928,plain,
    ( r1_tarski(sK10,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_1747])).

cnf(c_5113,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK10,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5111,c_2928])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1752,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3808,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2928,c_1752])).

cnf(c_6368,plain,
    ( r2_hidden(k2_mcart_1(sK11),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_3808])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1755,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6379,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6368,c_1755])).

cnf(c_6709,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5111,c_6379])).

cnf(c_6710,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6709])).

cnf(c_8557,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5113,c_68,c_6709])).

cnf(c_8558,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8557])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1734,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8569,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8558,c_1734])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1756,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2787,plain,
    ( r2_hidden(sK9,k1_zfmisc_1(sK5)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1745])).

cnf(c_584,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK5) != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_585,plain,
    ( r2_hidden(sK9,k1_zfmisc_1(sK5))
    | v1_xboole_0(k1_zfmisc_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_591,plain,
    ( r2_hidden(sK9,k1_zfmisc_1(sK5)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_585,c_10])).

cnf(c_593,plain,
    ( r2_hidden(sK9,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_3051,plain,
    ( r2_hidden(sK9,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2787,c_593])).

cnf(c_3056,plain,
    ( r1_tarski(sK9,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3051,c_1747])).

cnf(c_4177,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3056,c_1752])).

cnf(c_6712,plain,
    ( r2_hidden(sK0(sK9),sK5) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1756,c_4177])).

cnf(c_4304,plain,
    ( v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2698,c_1755])).

cnf(c_7907,plain,
    ( r2_hidden(sK0(sK9),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6712,c_4304])).

cnf(c_7911,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7907,c_1755])).

cnf(c_8561,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8558,c_7911])).

cnf(c_8572,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8561])).

cnf(c_8582,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8569,c_68,c_8561])).

cnf(c_8583,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8582])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1733,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2788,plain,
    ( r2_hidden(sK8,k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1733,c_1745])).

cnf(c_594,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK4) != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_595,plain,
    ( r2_hidden(sK8,k1_zfmisc_1(sK4))
    | v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_601,plain,
    ( r2_hidden(sK8,k1_zfmisc_1(sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_595,c_10])).

cnf(c_603,plain,
    ( r2_hidden(sK8,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_3059,plain,
    ( r2_hidden(sK8,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2788,c_603])).

cnf(c_3064,plain,
    ( r1_tarski(sK8,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3059,c_1747])).

cnf(c_4182,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3064,c_1752])).

cnf(c_8153,plain,
    ( r2_hidden(sK0(sK8),sK4) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1756,c_4182])).

cnf(c_4659,plain,
    ( v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4412,c_1755])).

cnf(c_8919,plain,
    ( r2_hidden(sK0(sK8),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8153,c_4659])).

cnf(c_8924,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8919,c_1755])).

cnf(c_8928,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8583,c_8924])).

cnf(c_68,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9257,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8928,c_68])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1732,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2789,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_1745])).

cnf(c_604,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK3) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_605,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_611,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_605,c_10])).

cnf(c_613,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_3163,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2789,c_613])).

cnf(c_3168,plain,
    ( r1_tarski(sK7,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3163,c_1747])).

cnf(c_4299,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_1752])).

cnf(c_8284,plain,
    ( r2_hidden(sK0(sK7),sK3) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1756,c_4299])).

cnf(c_5456,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4413,c_1755])).

cnf(c_9103,plain,
    ( r2_hidden(sK0(sK7),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8284,c_5456])).

cnf(c_9107,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9103,c_1755])).

cnf(c_9259,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9257,c_9107])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9259,c_68])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:44:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.07/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.07/0.98  
% 3.07/0.98  ------  iProver source info
% 3.07/0.98  
% 3.07/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.07/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.07/0.98  git: non_committed_changes: false
% 3.07/0.98  git: last_make_outside_of_git: false
% 3.07/0.98  
% 3.07/0.98  ------ 
% 3.07/0.98  
% 3.07/0.98  ------ Input Options
% 3.07/0.98  
% 3.07/0.98  --out_options                           all
% 3.07/0.98  --tptp_safe_out                         true
% 3.07/0.98  --problem_path                          ""
% 3.07/0.98  --include_path                          ""
% 3.07/0.98  --clausifier                            res/vclausify_rel
% 3.07/0.98  --clausifier_options                    ""
% 3.07/0.98  --stdin                                 false
% 3.07/0.98  --stats_out                             all
% 3.07/0.98  
% 3.07/0.98  ------ General Options
% 3.07/0.98  
% 3.07/0.98  --fof                                   false
% 3.07/0.98  --time_out_real                         305.
% 3.07/0.98  --time_out_virtual                      -1.
% 3.07/0.98  --symbol_type_check                     false
% 3.07/0.98  --clausify_out                          false
% 3.07/0.98  --sig_cnt_out                           false
% 3.07/0.98  --trig_cnt_out                          false
% 3.07/0.98  --trig_cnt_out_tolerance                1.
% 3.07/0.98  --trig_cnt_out_sk_spl                   false
% 3.07/0.98  --abstr_cl_out                          false
% 3.07/0.98  
% 3.07/0.98  ------ Global Options
% 3.07/0.98  
% 3.07/0.98  --schedule                              default
% 3.07/0.98  --add_important_lit                     false
% 3.07/0.98  --prop_solver_per_cl                    1000
% 3.07/0.98  --min_unsat_core                        false
% 3.07/0.98  --soft_assumptions                      false
% 3.07/0.98  --soft_lemma_size                       3
% 3.07/0.98  --prop_impl_unit_size                   0
% 3.07/0.98  --prop_impl_unit                        []
% 3.07/0.98  --share_sel_clauses                     true
% 3.07/0.98  --reset_solvers                         false
% 3.07/0.98  --bc_imp_inh                            [conj_cone]
% 3.07/0.98  --conj_cone_tolerance                   3.
% 3.07/0.98  --extra_neg_conj                        none
% 3.07/0.98  --large_theory_mode                     true
% 3.07/0.98  --prolific_symb_bound                   200
% 3.07/0.98  --lt_threshold                          2000
% 3.07/0.98  --clause_weak_htbl                      true
% 3.07/0.98  --gc_record_bc_elim                     false
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing Options
% 3.07/0.98  
% 3.07/0.98  --preprocessing_flag                    true
% 3.07/0.98  --time_out_prep_mult                    0.1
% 3.07/0.98  --splitting_mode                        input
% 3.07/0.98  --splitting_grd                         true
% 3.07/0.98  --splitting_cvd                         false
% 3.07/0.98  --splitting_cvd_svl                     false
% 3.07/0.98  --splitting_nvd                         32
% 3.07/0.98  --sub_typing                            true
% 3.07/0.98  --prep_gs_sim                           true
% 3.07/0.98  --prep_unflatten                        true
% 3.07/0.98  --prep_res_sim                          true
% 3.07/0.98  --prep_upred                            true
% 3.07/0.98  --prep_sem_filter                       exhaustive
% 3.07/0.98  --prep_sem_filter_out                   false
% 3.07/0.98  --pred_elim                             true
% 3.07/0.98  --res_sim_input                         true
% 3.07/0.98  --eq_ax_congr_red                       true
% 3.07/0.98  --pure_diseq_elim                       true
% 3.07/0.98  --brand_transform                       false
% 3.07/0.98  --non_eq_to_eq                          false
% 3.07/0.98  --prep_def_merge                        true
% 3.07/0.98  --prep_def_merge_prop_impl              false
% 3.07/0.98  --prep_def_merge_mbd                    true
% 3.07/0.98  --prep_def_merge_tr_red                 false
% 3.07/0.98  --prep_def_merge_tr_cl                  false
% 3.07/0.98  --smt_preprocessing                     true
% 3.07/0.98  --smt_ac_axioms                         fast
% 3.07/0.98  --preprocessed_out                      false
% 3.07/0.98  --preprocessed_stats                    false
% 3.07/0.98  
% 3.07/0.98  ------ Abstraction refinement Options
% 3.07/0.98  
% 3.07/0.98  --abstr_ref                             []
% 3.07/0.98  --abstr_ref_prep                        false
% 3.07/0.98  --abstr_ref_until_sat                   false
% 3.07/0.98  --abstr_ref_sig_restrict                funpre
% 3.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.98  --abstr_ref_under                       []
% 3.07/0.98  
% 3.07/0.98  ------ SAT Options
% 3.07/0.98  
% 3.07/0.98  --sat_mode                              false
% 3.07/0.98  --sat_fm_restart_options                ""
% 3.07/0.98  --sat_gr_def                            false
% 3.07/0.98  --sat_epr_types                         true
% 3.07/0.98  --sat_non_cyclic_types                  false
% 3.07/0.98  --sat_finite_models                     false
% 3.07/0.98  --sat_fm_lemmas                         false
% 3.07/0.98  --sat_fm_prep                           false
% 3.07/0.98  --sat_fm_uc_incr                        true
% 3.07/0.98  --sat_out_model                         small
% 3.07/0.98  --sat_out_clauses                       false
% 3.07/0.98  
% 3.07/0.98  ------ QBF Options
% 3.07/0.98  
% 3.07/0.98  --qbf_mode                              false
% 3.07/0.98  --qbf_elim_univ                         false
% 3.07/0.98  --qbf_dom_inst                          none
% 3.07/0.98  --qbf_dom_pre_inst                      false
% 3.07/0.98  --qbf_sk_in                             false
% 3.07/0.98  --qbf_pred_elim                         true
% 3.07/0.98  --qbf_split                             512
% 3.07/0.98  
% 3.07/0.98  ------ BMC1 Options
% 3.07/0.98  
% 3.07/0.98  --bmc1_incremental                      false
% 3.07/0.98  --bmc1_axioms                           reachable_all
% 3.07/0.98  --bmc1_min_bound                        0
% 3.07/0.98  --bmc1_max_bound                        -1
% 3.07/0.98  --bmc1_max_bound_default                -1
% 3.07/0.98  --bmc1_symbol_reachability              true
% 3.07/0.98  --bmc1_property_lemmas                  false
% 3.07/0.98  --bmc1_k_induction                      false
% 3.07/0.98  --bmc1_non_equiv_states                 false
% 3.07/0.98  --bmc1_deadlock                         false
% 3.07/0.98  --bmc1_ucm                              false
% 3.07/0.98  --bmc1_add_unsat_core                   none
% 3.07/0.98  --bmc1_unsat_core_children              false
% 3.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.98  --bmc1_out_stat                         full
% 3.07/0.98  --bmc1_ground_init                      false
% 3.07/0.98  --bmc1_pre_inst_next_state              false
% 3.07/0.98  --bmc1_pre_inst_state                   false
% 3.07/0.98  --bmc1_pre_inst_reach_state             false
% 3.07/0.98  --bmc1_out_unsat_core                   false
% 3.07/0.98  --bmc1_aig_witness_out                  false
% 3.07/0.98  --bmc1_verbose                          false
% 3.07/0.98  --bmc1_dump_clauses_tptp                false
% 3.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.98  --bmc1_dump_file                        -
% 3.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.98  --bmc1_ucm_extend_mode                  1
% 3.07/0.98  --bmc1_ucm_init_mode                    2
% 3.07/0.98  --bmc1_ucm_cone_mode                    none
% 3.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.98  --bmc1_ucm_relax_model                  4
% 3.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.98  --bmc1_ucm_layered_model                none
% 3.07/0.99  --bmc1_ucm_max_lemma_size               10
% 3.07/0.99  
% 3.07/0.99  ------ AIG Options
% 3.07/0.99  
% 3.07/0.99  --aig_mode                              false
% 3.07/0.99  
% 3.07/0.99  ------ Instantiation Options
% 3.07/0.99  
% 3.07/0.99  --instantiation_flag                    true
% 3.07/0.99  --inst_sos_flag                         true
% 3.07/0.99  --inst_sos_phase                        true
% 3.07/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.99  --inst_lit_sel_side                     num_symb
% 3.07/0.99  --inst_solver_per_active                1400
% 3.07/0.99  --inst_solver_calls_frac                1.
% 3.07/0.99  --inst_passive_queue_type               priority_queues
% 3.07/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/0.99  --inst_passive_queues_freq              [25;2]
% 3.07/0.99  --inst_dismatching                      true
% 3.07/0.99  --inst_eager_unprocessed_to_passive     true
% 3.07/0.99  --inst_prop_sim_given                   true
% 3.07/0.99  --inst_prop_sim_new                     false
% 3.07/0.99  --inst_subs_new                         false
% 3.07/0.99  --inst_eq_res_simp                      false
% 3.07/0.99  --inst_subs_given                       false
% 3.07/0.99  --inst_orphan_elimination               true
% 3.07/0.99  --inst_learning_loop_flag               true
% 3.07/0.99  --inst_learning_start                   3000
% 3.07/0.99  --inst_learning_factor                  2
% 3.07/0.99  --inst_start_prop_sim_after_learn       3
% 3.07/0.99  --inst_sel_renew                        solver
% 3.07/0.99  --inst_lit_activity_flag                true
% 3.07/0.99  --inst_restr_to_given                   false
% 3.07/0.99  --inst_activity_threshold               500
% 3.07/0.99  --inst_out_proof                        true
% 3.07/0.99  
% 3.07/0.99  ------ Resolution Options
% 3.07/0.99  
% 3.07/0.99  --resolution_flag                       true
% 3.07/0.99  --res_lit_sel                           adaptive
% 3.07/0.99  --res_lit_sel_side                      none
% 3.07/0.99  --res_ordering                          kbo
% 3.07/0.99  --res_to_prop_solver                    active
% 3.07/0.99  --res_prop_simpl_new                    false
% 3.07/0.99  --res_prop_simpl_given                  true
% 3.07/0.99  --res_passive_queue_type                priority_queues
% 3.07/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/0.99  --res_passive_queues_freq               [15;5]
% 3.07/0.99  --res_forward_subs                      full
% 3.07/0.99  --res_backward_subs                     full
% 3.07/0.99  --res_forward_subs_resolution           true
% 3.07/0.99  --res_backward_subs_resolution          true
% 3.07/0.99  --res_orphan_elimination                true
% 3.07/0.99  --res_time_limit                        2.
% 3.07/0.99  --res_out_proof                         true
% 3.07/0.99  
% 3.07/0.99  ------ Superposition Options
% 3.07/0.99  
% 3.07/0.99  --superposition_flag                    true
% 3.07/0.99  --sup_passive_queue_type                priority_queues
% 3.07/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.99  --demod_completeness_check              fast
% 3.07/0.99  --demod_use_ground                      true
% 3.07/0.99  --sup_to_prop_solver                    passive
% 3.07/0.99  --sup_prop_simpl_new                    true
% 3.07/0.99  --sup_prop_simpl_given                  true
% 3.07/0.99  --sup_fun_splitting                     true
% 3.07/0.99  --sup_smt_interval                      50000
% 3.07/0.99  
% 3.07/0.99  ------ Superposition Simplification Setup
% 3.07/0.99  
% 3.07/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.07/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.07/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.07/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.07/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.07/0.99  --sup_immed_triv                        [TrivRules]
% 3.07/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.99  --sup_immed_bw_main                     []
% 3.07/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.07/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.99  --sup_input_bw                          []
% 3.07/0.99  
% 3.07/0.99  ------ Combination Options
% 3.07/0.99  
% 3.07/0.99  --comb_res_mult                         3
% 3.07/0.99  --comb_sup_mult                         2
% 3.07/0.99  --comb_inst_mult                        10
% 3.07/0.99  
% 3.07/0.99  ------ Debug Options
% 3.07/0.99  
% 3.07/0.99  --dbg_backtrace                         false
% 3.07/0.99  --dbg_dump_prop_clauses                 false
% 3.07/0.99  --dbg_dump_prop_clauses_file            -
% 3.07/0.99  --dbg_out_stat                          false
% 3.07/0.99  ------ Parsing...
% 3.07/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.07/0.99  
% 3.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.07/0.99  
% 3.07/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.07/0.99  
% 3.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.07/0.99  ------ Proving...
% 3.07/0.99  ------ Problem Properties 
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  clauses                                 25
% 3.07/0.99  conjectures                             7
% 3.07/0.99  EPR                                     4
% 3.07/0.99  Horn                                    17
% 3.07/0.99  unary                                   8
% 3.07/0.99  binary                                  8
% 3.07/0.99  lits                                    64
% 3.07/0.99  lits eq                                 22
% 3.07/0.99  fd_pure                                 0
% 3.07/0.99  fd_pseudo                               0
% 3.07/0.99  fd_cond                                 4
% 3.07/0.99  fd_pseudo_cond                          2
% 3.07/0.99  AC symbols                              0
% 3.07/0.99  
% 3.07/0.99  ------ Schedule dynamic 5 is on 
% 3.07/0.99  
% 3.07/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  ------ 
% 3.07/0.99  Current options:
% 3.07/0.99  ------ 
% 3.07/0.99  
% 3.07/0.99  ------ Input Options
% 3.07/0.99  
% 3.07/0.99  --out_options                           all
% 3.07/0.99  --tptp_safe_out                         true
% 3.07/0.99  --problem_path                          ""
% 3.07/0.99  --include_path                          ""
% 3.07/0.99  --clausifier                            res/vclausify_rel
% 3.07/0.99  --clausifier_options                    ""
% 3.07/0.99  --stdin                                 false
% 3.07/0.99  --stats_out                             all
% 3.07/0.99  
% 3.07/0.99  ------ General Options
% 3.07/0.99  
% 3.07/0.99  --fof                                   false
% 3.07/0.99  --time_out_real                         305.
% 3.07/0.99  --time_out_virtual                      -1.
% 3.07/0.99  --symbol_type_check                     false
% 3.07/0.99  --clausify_out                          false
% 3.07/0.99  --sig_cnt_out                           false
% 3.07/0.99  --trig_cnt_out                          false
% 3.07/0.99  --trig_cnt_out_tolerance                1.
% 3.07/0.99  --trig_cnt_out_sk_spl                   false
% 3.07/0.99  --abstr_cl_out                          false
% 3.07/0.99  
% 3.07/0.99  ------ Global Options
% 3.07/0.99  
% 3.07/0.99  --schedule                              default
% 3.07/0.99  --add_important_lit                     false
% 3.07/0.99  --prop_solver_per_cl                    1000
% 3.07/0.99  --min_unsat_core                        false
% 3.07/0.99  --soft_assumptions                      false
% 3.07/0.99  --soft_lemma_size                       3
% 3.07/0.99  --prop_impl_unit_size                   0
% 3.07/0.99  --prop_impl_unit                        []
% 3.07/0.99  --share_sel_clauses                     true
% 3.07/0.99  --reset_solvers                         false
% 3.07/0.99  --bc_imp_inh                            [conj_cone]
% 3.07/0.99  --conj_cone_tolerance                   3.
% 3.07/0.99  --extra_neg_conj                        none
% 3.07/0.99  --large_theory_mode                     true
% 3.07/0.99  --prolific_symb_bound                   200
% 3.07/0.99  --lt_threshold                          2000
% 3.07/0.99  --clause_weak_htbl                      true
% 3.07/0.99  --gc_record_bc_elim                     false
% 3.07/0.99  
% 3.07/0.99  ------ Preprocessing Options
% 3.07/0.99  
% 3.07/0.99  --preprocessing_flag                    true
% 3.07/0.99  --time_out_prep_mult                    0.1
% 3.07/0.99  --splitting_mode                        input
% 3.07/0.99  --splitting_grd                         true
% 3.07/0.99  --splitting_cvd                         false
% 3.07/0.99  --splitting_cvd_svl                     false
% 3.07/0.99  --splitting_nvd                         32
% 3.07/0.99  --sub_typing                            true
% 3.07/0.99  --prep_gs_sim                           true
% 3.07/0.99  --prep_unflatten                        true
% 3.07/0.99  --prep_res_sim                          true
% 3.07/0.99  --prep_upred                            true
% 3.07/0.99  --prep_sem_filter                       exhaustive
% 3.07/0.99  --prep_sem_filter_out                   false
% 3.07/0.99  --pred_elim                             true
% 3.07/0.99  --res_sim_input                         true
% 3.07/0.99  --eq_ax_congr_red                       true
% 3.07/0.99  --pure_diseq_elim                       true
% 3.07/0.99  --brand_transform                       false
% 3.07/0.99  --non_eq_to_eq                          false
% 3.07/0.99  --prep_def_merge                        true
% 3.07/0.99  --prep_def_merge_prop_impl              false
% 3.07/0.99  --prep_def_merge_mbd                    true
% 3.07/0.99  --prep_def_merge_tr_red                 false
% 3.07/0.99  --prep_def_merge_tr_cl                  false
% 3.07/0.99  --smt_preprocessing                     true
% 3.07/0.99  --smt_ac_axioms                         fast
% 3.07/0.99  --preprocessed_out                      false
% 3.07/0.99  --preprocessed_stats                    false
% 3.07/0.99  
% 3.07/0.99  ------ Abstraction refinement Options
% 3.07/0.99  
% 3.07/0.99  --abstr_ref                             []
% 3.07/0.99  --abstr_ref_prep                        false
% 3.07/0.99  --abstr_ref_until_sat                   false
% 3.07/0.99  --abstr_ref_sig_restrict                funpre
% 3.07/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.99  --abstr_ref_under                       []
% 3.07/0.99  
% 3.07/0.99  ------ SAT Options
% 3.07/0.99  
% 3.07/0.99  --sat_mode                              false
% 3.07/0.99  --sat_fm_restart_options                ""
% 3.07/0.99  --sat_gr_def                            false
% 3.07/0.99  --sat_epr_types                         true
% 3.07/0.99  --sat_non_cyclic_types                  false
% 3.07/0.99  --sat_finite_models                     false
% 3.07/0.99  --sat_fm_lemmas                         false
% 3.07/0.99  --sat_fm_prep                           false
% 3.07/0.99  --sat_fm_uc_incr                        true
% 3.07/0.99  --sat_out_model                         small
% 3.07/0.99  --sat_out_clauses                       false
% 3.07/0.99  
% 3.07/0.99  ------ QBF Options
% 3.07/0.99  
% 3.07/0.99  --qbf_mode                              false
% 3.07/0.99  --qbf_elim_univ                         false
% 3.07/0.99  --qbf_dom_inst                          none
% 3.07/0.99  --qbf_dom_pre_inst                      false
% 3.07/0.99  --qbf_sk_in                             false
% 3.07/0.99  --qbf_pred_elim                         true
% 3.07/0.99  --qbf_split                             512
% 3.07/0.99  
% 3.07/0.99  ------ BMC1 Options
% 3.07/0.99  
% 3.07/0.99  --bmc1_incremental                      false
% 3.07/0.99  --bmc1_axioms                           reachable_all
% 3.07/0.99  --bmc1_min_bound                        0
% 3.07/0.99  --bmc1_max_bound                        -1
% 3.07/0.99  --bmc1_max_bound_default                -1
% 3.07/0.99  --bmc1_symbol_reachability              true
% 3.07/0.99  --bmc1_property_lemmas                  false
% 3.07/0.99  --bmc1_k_induction                      false
% 3.07/0.99  --bmc1_non_equiv_states                 false
% 3.07/0.99  --bmc1_deadlock                         false
% 3.07/0.99  --bmc1_ucm                              false
% 3.07/0.99  --bmc1_add_unsat_core                   none
% 3.07/0.99  --bmc1_unsat_core_children              false
% 3.07/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.99  --bmc1_out_stat                         full
% 3.07/0.99  --bmc1_ground_init                      false
% 3.07/0.99  --bmc1_pre_inst_next_state              false
% 3.07/0.99  --bmc1_pre_inst_state                   false
% 3.07/0.99  --bmc1_pre_inst_reach_state             false
% 3.07/0.99  --bmc1_out_unsat_core                   false
% 3.07/0.99  --bmc1_aig_witness_out                  false
% 3.07/0.99  --bmc1_verbose                          false
% 3.07/0.99  --bmc1_dump_clauses_tptp                false
% 3.07/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.99  --bmc1_dump_file                        -
% 3.07/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.99  --bmc1_ucm_extend_mode                  1
% 3.07/0.99  --bmc1_ucm_init_mode                    2
% 3.07/0.99  --bmc1_ucm_cone_mode                    none
% 3.07/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.99  --bmc1_ucm_relax_model                  4
% 3.07/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.99  --bmc1_ucm_layered_model                none
% 3.07/0.99  --bmc1_ucm_max_lemma_size               10
% 3.07/0.99  
% 3.07/0.99  ------ AIG Options
% 3.07/0.99  
% 3.07/0.99  --aig_mode                              false
% 3.07/0.99  
% 3.07/0.99  ------ Instantiation Options
% 3.07/0.99  
% 3.07/0.99  --instantiation_flag                    true
% 3.07/0.99  --inst_sos_flag                         true
% 3.07/0.99  --inst_sos_phase                        true
% 3.07/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.99  --inst_lit_sel_side                     none
% 3.07/0.99  --inst_solver_per_active                1400
% 3.07/0.99  --inst_solver_calls_frac                1.
% 3.07/0.99  --inst_passive_queue_type               priority_queues
% 3.07/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/0.99  --inst_passive_queues_freq              [25;2]
% 3.07/0.99  --inst_dismatching                      true
% 3.07/0.99  --inst_eager_unprocessed_to_passive     true
% 3.07/0.99  --inst_prop_sim_given                   true
% 3.07/0.99  --inst_prop_sim_new                     false
% 3.07/0.99  --inst_subs_new                         false
% 3.07/0.99  --inst_eq_res_simp                      false
% 3.07/0.99  --inst_subs_given                       false
% 3.07/0.99  --inst_orphan_elimination               true
% 3.07/0.99  --inst_learning_loop_flag               true
% 3.07/0.99  --inst_learning_start                   3000
% 3.07/0.99  --inst_learning_factor                  2
% 3.07/0.99  --inst_start_prop_sim_after_learn       3
% 3.07/0.99  --inst_sel_renew                        solver
% 3.07/0.99  --inst_lit_activity_flag                true
% 3.07/0.99  --inst_restr_to_given                   false
% 3.07/0.99  --inst_activity_threshold               500
% 3.07/0.99  --inst_out_proof                        true
% 3.07/0.99  
% 3.07/0.99  ------ Resolution Options
% 3.07/0.99  
% 3.07/0.99  --resolution_flag                       false
% 3.07/0.99  --res_lit_sel                           adaptive
% 3.07/0.99  --res_lit_sel_side                      none
% 3.07/0.99  --res_ordering                          kbo
% 3.07/0.99  --res_to_prop_solver                    active
% 3.07/0.99  --res_prop_simpl_new                    false
% 3.07/0.99  --res_prop_simpl_given                  true
% 3.07/0.99  --res_passive_queue_type                priority_queues
% 3.07/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/0.99  --res_passive_queues_freq               [15;5]
% 3.07/0.99  --res_forward_subs                      full
% 3.07/0.99  --res_backward_subs                     full
% 3.07/0.99  --res_forward_subs_resolution           true
% 3.07/0.99  --res_backward_subs_resolution          true
% 3.07/0.99  --res_orphan_elimination                true
% 3.07/0.99  --res_time_limit                        2.
% 3.07/0.99  --res_out_proof                         true
% 3.07/0.99  
% 3.07/0.99  ------ Superposition Options
% 3.07/0.99  
% 3.07/0.99  --superposition_flag                    true
% 3.07/0.99  --sup_passive_queue_type                priority_queues
% 3.07/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.99  --demod_completeness_check              fast
% 3.07/0.99  --demod_use_ground                      true
% 3.07/0.99  --sup_to_prop_solver                    passive
% 3.07/0.99  --sup_prop_simpl_new                    true
% 3.07/0.99  --sup_prop_simpl_given                  true
% 3.07/0.99  --sup_fun_splitting                     true
% 3.07/0.99  --sup_smt_interval                      50000
% 3.07/0.99  
% 3.07/0.99  ------ Superposition Simplification Setup
% 3.07/0.99  
% 3.07/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.07/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.07/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.07/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.07/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.07/0.99  --sup_immed_triv                        [TrivRules]
% 3.07/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.99  --sup_immed_bw_main                     []
% 3.07/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.07/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.99  --sup_input_bw                          []
% 3.07/0.99  
% 3.07/0.99  ------ Combination Options
% 3.07/0.99  
% 3.07/0.99  --comb_res_mult                         3
% 3.07/0.99  --comb_sup_mult                         2
% 3.07/0.99  --comb_inst_mult                        10
% 3.07/0.99  
% 3.07/0.99  ------ Debug Options
% 3.07/0.99  
% 3.07/0.99  --dbg_backtrace                         false
% 3.07/0.99  --dbg_dump_prop_clauses                 false
% 3.07/0.99  --dbg_dump_prop_clauses_file            -
% 3.07/0.99  --dbg_out_stat                          false
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  ------ Proving...
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  % SZS status Theorem for theBenchmark.p
% 3.07/0.99  
% 3.07/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.07/0.99  
% 3.07/0.99  fof(f11,conjecture,(
% 3.07/0.99    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f12,negated_conjecture,(
% 3.07/0.99    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 3.07/0.99    inference(negated_conjecture,[],[f11])).
% 3.07/0.99  
% 3.07/0.99  fof(f18,plain,(
% 3.07/0.99    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 3.07/0.99    inference(ennf_transformation,[],[f12])).
% 3.07/0.99  
% 3.07/0.99  fof(f19,plain,(
% 3.07/0.99    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 3.07/0.99    inference(flattening,[],[f18])).
% 3.07/0.99  
% 3.07/0.99  fof(f36,plain,(
% 3.07/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) => ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,sK11),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,sK11),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,sK11),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,sK11),X4)) & r2_hidden(sK11,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(sK11,k4_zfmisc_1(X0,X1,X2,X3)))) )),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f35,plain,(
% 3.07/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),sK10) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,sK10)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(sK10,k1_zfmisc_1(X3)))) )),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f34,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),sK9) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,sK9,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(sK9,k1_zfmisc_1(X2)))) )),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f33,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),sK8) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,sK8,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(sK8,k1_zfmisc_1(X1)))) )),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f32,plain,(
% 3.07/0.99    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,X8),X7) | ~r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,X8),X6) | ~r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,X8),X5) | ~r2_hidden(k8_mcart_1(sK3,sK4,sK5,sK6,X8),sK7)) & r2_hidden(X8,k4_zfmisc_1(sK7,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK3,sK4,sK5,sK6))) & m1_subset_1(X7,k1_zfmisc_1(sK6))) & m1_subset_1(X6,k1_zfmisc_1(sK5))) & m1_subset_1(X5,k1_zfmisc_1(sK4))) & m1_subset_1(sK7,k1_zfmisc_1(sK3)))),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f37,plain,(
% 3.07/0.99    (((((~r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) | ~r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9) | ~r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,sK11),sK8) | ~r2_hidden(k8_mcart_1(sK3,sK4,sK5,sK6,sK11),sK7)) & r2_hidden(sK11,k4_zfmisc_1(sK7,sK8,sK9,sK10)) & m1_subset_1(sK11,k4_zfmisc_1(sK3,sK4,sK5,sK6))) & m1_subset_1(sK10,k1_zfmisc_1(sK6))) & m1_subset_1(sK9,k1_zfmisc_1(sK5))) & m1_subset_1(sK8,k1_zfmisc_1(sK4))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 3.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9,sK10,sK11])],[f19,f36,f35,f34,f33,f32])).
% 3.07/0.99  
% 3.07/0.99  fof(f62,plain,(
% 3.07/0.99    m1_subset_1(sK11,k4_zfmisc_1(sK3,sK4,sK5,sK6))),
% 3.07/0.99    inference(cnf_transformation,[],[f37])).
% 3.07/0.99  
% 3.07/0.99  fof(f8,axiom,(
% 3.07/0.99    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f51,plain,(
% 3.07/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f8])).
% 3.07/0.99  
% 3.07/0.99  fof(f7,axiom,(
% 3.07/0.99    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f50,plain,(
% 3.07/0.99    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f7])).
% 3.07/0.99  
% 3.07/0.99  fof(f65,plain,(
% 3.07/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.07/0.99    inference(definition_unfolding,[],[f51,f50])).
% 3.07/0.99  
% 3.07/0.99  fof(f71,plain,(
% 3.07/0.99    m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6))),
% 3.07/0.99    inference(definition_unfolding,[],[f62,f65])).
% 3.07/0.99  
% 3.07/0.99  fof(f10,axiom,(
% 3.07/0.99    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f17,plain,(
% 3.07/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.07/0.99    inference(ennf_transformation,[],[f10])).
% 3.07/0.99  
% 3.07/0.99  fof(f57,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(cnf_transformation,[],[f17])).
% 3.07/0.99  
% 3.07/0.99  fof(f66,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(definition_unfolding,[],[f57,f65])).
% 3.07/0.99  
% 3.07/0.99  fof(f56,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(cnf_transformation,[],[f17])).
% 3.07/0.99  
% 3.07/0.99  fof(f67,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(definition_unfolding,[],[f56,f65])).
% 3.07/0.99  
% 3.07/0.99  fof(f55,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(cnf_transformation,[],[f17])).
% 3.07/0.99  
% 3.07/0.99  fof(f68,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(definition_unfolding,[],[f55,f65])).
% 3.07/0.99  
% 3.07/0.99  fof(f54,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(cnf_transformation,[],[f17])).
% 3.07/0.99  
% 3.07/0.99  fof(f69,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(definition_unfolding,[],[f54,f65])).
% 3.07/0.99  
% 3.07/0.99  fof(f64,plain,(
% 3.07/0.99    ~r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) | ~r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9) | ~r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,sK11),sK8) | ~r2_hidden(k8_mcart_1(sK3,sK4,sK5,sK6,sK11),sK7)),
% 3.07/0.99    inference(cnf_transformation,[],[f37])).
% 3.07/0.99  
% 3.07/0.99  fof(f63,plain,(
% 3.07/0.99    r2_hidden(sK11,k4_zfmisc_1(sK7,sK8,sK9,sK10))),
% 3.07/0.99    inference(cnf_transformation,[],[f37])).
% 3.07/0.99  
% 3.07/0.99  fof(f70,plain,(
% 3.07/0.99    r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10))),
% 3.07/0.99    inference(definition_unfolding,[],[f63,f65])).
% 3.07/0.99  
% 3.07/0.99  fof(f9,axiom,(
% 3.07/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f16,plain,(
% 3.07/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.07/0.99    inference(ennf_transformation,[],[f9])).
% 3.07/0.99  
% 3.07/0.99  fof(f52,plain,(
% 3.07/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.07/0.99    inference(cnf_transformation,[],[f16])).
% 3.07/0.99  
% 3.07/0.99  fof(f53,plain,(
% 3.07/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.07/0.99    inference(cnf_transformation,[],[f16])).
% 3.07/0.99  
% 3.07/0.99  fof(f61,plain,(
% 3.07/0.99    m1_subset_1(sK10,k1_zfmisc_1(sK6))),
% 3.07/0.99    inference(cnf_transformation,[],[f37])).
% 3.07/0.99  
% 3.07/0.99  fof(f6,axiom,(
% 3.07/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f14,plain,(
% 3.07/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.07/0.99    inference(ennf_transformation,[],[f6])).
% 3.07/0.99  
% 3.07/0.99  fof(f15,plain,(
% 3.07/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.07/0.99    inference(flattening,[],[f14])).
% 3.07/0.99  
% 3.07/0.99  fof(f49,plain,(
% 3.07/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f15])).
% 3.07/0.99  
% 3.07/0.99  fof(f5,axiom,(
% 3.07/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f48,plain,(
% 3.07/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.07/0.99    inference(cnf_transformation,[],[f5])).
% 3.07/0.99  
% 3.07/0.99  fof(f4,axiom,(
% 3.07/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f28,plain,(
% 3.07/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.07/0.99    inference(nnf_transformation,[],[f4])).
% 3.07/0.99  
% 3.07/0.99  fof(f29,plain,(
% 3.07/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.07/0.99    inference(rectify,[],[f28])).
% 3.07/0.99  
% 3.07/0.99  fof(f30,plain,(
% 3.07/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f31,plain,(
% 3.07/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 3.07/0.99  
% 3.07/0.99  fof(f44,plain,(
% 3.07/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.07/0.99    inference(cnf_transformation,[],[f31])).
% 3.07/0.99  
% 3.07/0.99  fof(f73,plain,(
% 3.07/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.07/0.99    inference(equality_resolution,[],[f44])).
% 3.07/0.99  
% 3.07/0.99  fof(f3,axiom,(
% 3.07/0.99    v1_xboole_0(k1_xboole_0)),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f43,plain,(
% 3.07/0.99    v1_xboole_0(k1_xboole_0)),
% 3.07/0.99    inference(cnf_transformation,[],[f3])).
% 3.07/0.99  
% 3.07/0.99  fof(f2,axiom,(
% 3.07/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f13,plain,(
% 3.07/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.07/0.99    inference(ennf_transformation,[],[f2])).
% 3.07/0.99  
% 3.07/0.99  fof(f24,plain,(
% 3.07/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.07/0.99    inference(nnf_transformation,[],[f13])).
% 3.07/0.99  
% 3.07/0.99  fof(f25,plain,(
% 3.07/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.07/0.99    inference(rectify,[],[f24])).
% 3.07/0.99  
% 3.07/0.99  fof(f26,plain,(
% 3.07/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f27,plain,(
% 3.07/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 3.07/0.99  
% 3.07/0.99  fof(f40,plain,(
% 3.07/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f27])).
% 3.07/0.99  
% 3.07/0.99  fof(f1,axiom,(
% 3.07/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f20,plain,(
% 3.07/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.07/0.99    inference(nnf_transformation,[],[f1])).
% 3.07/0.99  
% 3.07/0.99  fof(f21,plain,(
% 3.07/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.07/0.99    inference(rectify,[],[f20])).
% 3.07/0.99  
% 3.07/0.99  fof(f22,plain,(
% 3.07/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f23,plain,(
% 3.07/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 3.07/0.99  
% 3.07/0.99  fof(f38,plain,(
% 3.07/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f23])).
% 3.07/0.99  
% 3.07/0.99  fof(f60,plain,(
% 3.07/0.99    m1_subset_1(sK9,k1_zfmisc_1(sK5))),
% 3.07/0.99    inference(cnf_transformation,[],[f37])).
% 3.07/0.99  
% 3.07/0.99  fof(f39,plain,(
% 3.07/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f23])).
% 3.07/0.99  
% 3.07/0.99  fof(f59,plain,(
% 3.07/0.99    m1_subset_1(sK8,k1_zfmisc_1(sK4))),
% 3.07/0.99    inference(cnf_transformation,[],[f37])).
% 3.07/0.99  
% 3.07/0.99  fof(f58,plain,(
% 3.07/0.99    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 3.07/0.99    inference(cnf_transformation,[],[f37])).
% 3.07/0.99  
% 3.07/0.99  cnf(c_20,negated_conjecture,
% 3.07/0.99      ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6)) ),
% 3.07/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1736,plain,
% 3.07/0.99      ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_14,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.07/0.99      | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
% 3.07/0.99      | k1_xboole_0 = X4
% 3.07/0.99      | k1_xboole_0 = X3
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | k1_xboole_0 = X1 ),
% 3.07/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1742,plain,
% 3.07/0.99      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | k1_xboole_0 = X0
% 3.07/0.99      | k1_xboole_0 = X1
% 3.07/0.99      | k1_xboole_0 = X3
% 3.07/0.99      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3464,plain,
% 3.07/0.99      ( k11_mcart_1(sK3,sK4,sK5,sK6,sK11) = k2_mcart_1(sK11)
% 3.07/0.99      | sK6 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1736,c_1742]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_15,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.07/0.99      | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.07/0.99      | k1_xboole_0 = X4
% 3.07/0.99      | k1_xboole_0 = X3
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | k1_xboole_0 = X1 ),
% 3.07/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1741,plain,
% 3.07/0.99      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | k1_xboole_0 = X0
% 3.07/0.99      | k1_xboole_0 = X1
% 3.07/0.99      | k1_xboole_0 = X3
% 3.07/0.99      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3369,plain,
% 3.07/0.99      ( k10_mcart_1(sK3,sK4,sK5,sK6,sK11) = k2_mcart_1(k1_mcart_1(sK11))
% 3.07/0.99      | sK6 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1736,c_1741]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_16,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.07/0.99      | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 3.07/0.99      | k1_xboole_0 = X4
% 3.07/0.99      | k1_xboole_0 = X3
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | k1_xboole_0 = X1 ),
% 3.07/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1740,plain,
% 3.07/0.99      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | k1_xboole_0 = X0
% 3.07/0.99      | k1_xboole_0 = X1
% 3.07/0.99      | k1_xboole_0 = X3
% 3.07/0.99      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2574,plain,
% 3.07/0.99      ( k9_mcart_1(sK3,sK4,sK5,sK6,sK11) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK11)))
% 3.07/0.99      | sK6 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1736,c_1740]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_17,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.07/0.99      | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 3.07/0.99      | k1_xboole_0 = X4
% 3.07/0.99      | k1_xboole_0 = X3
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | k1_xboole_0 = X1 ),
% 3.07/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1739,plain,
% 3.07/0.99      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | k1_xboole_0 = X0
% 3.07/0.99      | k1_xboole_0 = X1
% 3.07/0.99      | k1_xboole_0 = X3
% 3.07/0.99      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2062,plain,
% 3.07/0.99      ( k8_mcart_1(sK3,sK4,sK5,sK6,sK11) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK11)))
% 3.07/0.99      | sK6 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1736,c_1739]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_18,negated_conjecture,
% 3.07/0.99      ( ~ r2_hidden(k8_mcart_1(sK3,sK4,sK5,sK6,sK11),sK7)
% 3.07/0.99      | ~ r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,sK11),sK8)
% 3.07/0.99      | ~ r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9)
% 3.07/0.99      | ~ r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) ),
% 3.07/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1738,plain,
% 3.07/0.99      ( r2_hidden(k8_mcart_1(sK3,sK4,sK5,sK6,sK11),sK7) != iProver_top
% 3.07/0.99      | r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,sK11),sK8) != iProver_top
% 3.07/0.99      | r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9) != iProver_top
% 3.07/0.99      | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2250,plain,
% 3.07/0.99      ( sK6 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k9_mcart_1(sK3,sK4,sK5,sK6,sK11),sK8) != iProver_top
% 3.07/0.99      | r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9) != iProver_top
% 3.07/0.99      | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top
% 3.07/0.99      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK11))),sK7) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2062,c_1738]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3285,plain,
% 3.07/0.99      ( sK6 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9) != iProver_top
% 3.07/0.99      | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top
% 3.07/0.99      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK11))),sK7) != iProver_top
% 3.07/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK11))),sK8) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2574,c_2250]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_19,negated_conjecture,
% 3.07/0.99      ( r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10)) ),
% 3.07/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1737,plain,
% 3.07/0.99      ( r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),sK10)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_13,plain,
% 3.07/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.07/0.99      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1743,plain,
% 3.07/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.07/0.99      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2408,plain,
% 3.07/0.99      ( r2_hidden(k1_mcart_1(sK11),k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1737,c_1743]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2415,plain,
% 3.07/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK11)),k2_zfmisc_1(sK7,sK8)) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2408,c_1743]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_12,plain,
% 3.07/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.07/0.99      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.07/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1744,plain,
% 3.07/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.07/0.99      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4412,plain,
% 3.07/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK11))),sK8) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2415,c_1744]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4413,plain,
% 3.07/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK11))),sK7) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2415,c_1743]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4994,plain,
% 3.07/0.99      ( sK6 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k10_mcart_1(sK3,sK4,sK5,sK6,sK11),sK9) != iProver_top
% 3.07/0.99      | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_3285,c_4412,c_4413]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4998,plain,
% 3.07/0.99      ( sK6 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top
% 3.07/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK11)),sK9) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3369,c_4994]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2698,plain,
% 3.07/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK11)),sK9) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2408,c_1744]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5001,plain,
% 3.07/0.99      ( r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK6 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_4998,c_2698]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5002,plain,
% 3.07/0.99      ( sK6 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k11_mcart_1(sK3,sK4,sK5,sK6,sK11),sK10) != iProver_top ),
% 3.07/0.99      inference(renaming,[status(thm)],[c_5001]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5005,plain,
% 3.07/0.99      ( sK6 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k2_mcart_1(sK11),sK10) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3464,c_5002]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2697,plain,
% 3.07/0.99      ( r2_hidden(k2_mcart_1(sK11),sK10) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1737,c_1744]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5110,plain,
% 3.07/0.99      ( sK3 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK6 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_5005,c_2697]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5111,plain,
% 3.07/0.99      ( sK6 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(renaming,[status(thm)],[c_5110]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_21,negated_conjecture,
% 3.07/0.99      ( m1_subset_1(sK10,k1_zfmisc_1(sK6)) ),
% 3.07/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1735,plain,
% 3.07/0.99      ( m1_subset_1(sK10,k1_zfmisc_1(sK6)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_11,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1745,plain,
% 3.07/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.07/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.07/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2786,plain,
% 3.07/0.99      ( r2_hidden(sK10,k1_zfmisc_1(sK6)) = iProver_top
% 3.07/0.99      | v1_xboole_0(k1_zfmisc_1(sK6)) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1735,c_1745]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_574,plain,
% 3.07/0.99      ( r2_hidden(X0,X1)
% 3.07/0.99      | v1_xboole_0(X1)
% 3.07/0.99      | k1_zfmisc_1(sK6) != X1
% 3.07/0.99      | sK10 != X0 ),
% 3.07/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_575,plain,
% 3.07/0.99      ( r2_hidden(sK10,k1_zfmisc_1(sK6))
% 3.07/0.99      | v1_xboole_0(k1_zfmisc_1(sK6)) ),
% 3.07/0.99      inference(unflattening,[status(thm)],[c_574]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_10,plain,
% 3.07/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.07/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_581,plain,
% 3.07/0.99      ( r2_hidden(sK10,k1_zfmisc_1(sK6)) ),
% 3.07/0.99      inference(forward_subsumption_resolution,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_575,c_10]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_583,plain,
% 3.07/0.99      ( r2_hidden(sK10,k1_zfmisc_1(sK6)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2923,plain,
% 3.07/0.99      ( r2_hidden(sK10,k1_zfmisc_1(sK6)) = iProver_top ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_2786,c_583]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_9,plain,
% 3.07/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.07/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1747,plain,
% 3.07/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.07/0.99      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2928,plain,
% 3.07/0.99      ( r1_tarski(sK10,sK6) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2923,c_1747]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5113,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r1_tarski(sK10,k1_xboole_0) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_5111,c_2928]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5,plain,
% 3.07/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4,plain,
% 3.07/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1752,plain,
% 3.07/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.07/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.07/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3808,plain,
% 3.07/0.99      ( r2_hidden(X0,sK10) != iProver_top
% 3.07/0.99      | r2_hidden(X0,sK6) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2928,c_1752]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6368,plain,
% 3.07/0.99      ( r2_hidden(k2_mcart_1(sK11),sK6) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2697,c_3808]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1,plain,
% 3.07/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1755,plain,
% 3.07/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.07/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6379,plain,
% 3.07/0.99      ( v1_xboole_0(sK6) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_6368,c_1755]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6709,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_5111,c_6379]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6710,plain,
% 3.07/0.99      ( ~ v1_xboole_0(k1_xboole_0)
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6709]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8557,plain,
% 3.07/0.99      ( sK3 = k1_xboole_0 | sK4 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_5113,c_68,c_6709]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8558,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0 | sK4 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(renaming,[status(thm)],[c_8557]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_22,negated_conjecture,
% 3.07/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(sK5)) ),
% 3.07/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1734,plain,
% 3.07/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(sK5)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8569,plain,
% 3.07/0.99      ( sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_8558,c_1734]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_0,plain,
% 3.07/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1756,plain,
% 3.07/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.07/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2787,plain,
% 3.07/0.99      ( r2_hidden(sK9,k1_zfmisc_1(sK5)) = iProver_top
% 3.07/0.99      | v1_xboole_0(k1_zfmisc_1(sK5)) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1734,c_1745]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_584,plain,
% 3.07/0.99      ( r2_hidden(X0,X1)
% 3.07/0.99      | v1_xboole_0(X1)
% 3.07/0.99      | k1_zfmisc_1(sK5) != X1
% 3.07/0.99      | sK9 != X0 ),
% 3.07/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_585,plain,
% 3.07/0.99      ( r2_hidden(sK9,k1_zfmisc_1(sK5)) | v1_xboole_0(k1_zfmisc_1(sK5)) ),
% 3.07/0.99      inference(unflattening,[status(thm)],[c_584]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_591,plain,
% 3.07/0.99      ( r2_hidden(sK9,k1_zfmisc_1(sK5)) ),
% 3.07/0.99      inference(forward_subsumption_resolution,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_585,c_10]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_593,plain,
% 3.07/0.99      ( r2_hidden(sK9,k1_zfmisc_1(sK5)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3051,plain,
% 3.07/0.99      ( r2_hidden(sK9,k1_zfmisc_1(sK5)) = iProver_top ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_2787,c_593]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3056,plain,
% 3.07/0.99      ( r1_tarski(sK9,sK5) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3051,c_1747]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4177,plain,
% 3.07/0.99      ( r2_hidden(X0,sK9) != iProver_top
% 3.07/0.99      | r2_hidden(X0,sK5) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3056,c_1752]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6712,plain,
% 3.07/0.99      ( r2_hidden(sK0(sK9),sK5) = iProver_top
% 3.07/0.99      | v1_xboole_0(sK9) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1756,c_4177]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4304,plain,
% 3.07/0.99      ( v1_xboole_0(sK9) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2698,c_1755]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_7907,plain,
% 3.07/0.99      ( r2_hidden(sK0(sK9),sK5) = iProver_top ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_6712,c_4304]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_7911,plain,
% 3.07/0.99      ( v1_xboole_0(sK5) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_7907,c_1755]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8561,plain,
% 3.07/0.99      ( sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_8558,c_7911]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8572,plain,
% 3.07/0.99      ( ~ v1_xboole_0(k1_xboole_0)
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_8561]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8582,plain,
% 3.07/0.99      ( sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_8569,c_68,c_8561]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8583,plain,
% 3.07/0.99      ( sK4 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(renaming,[status(thm)],[c_8582]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_23,negated_conjecture,
% 3.07/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
% 3.07/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1733,plain,
% 3.07/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2788,plain,
% 3.07/0.99      ( r2_hidden(sK8,k1_zfmisc_1(sK4)) = iProver_top
% 3.07/0.99      | v1_xboole_0(k1_zfmisc_1(sK4)) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1733,c_1745]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_594,plain,
% 3.07/0.99      ( r2_hidden(X0,X1)
% 3.07/0.99      | v1_xboole_0(X1)
% 3.07/0.99      | k1_zfmisc_1(sK4) != X1
% 3.07/0.99      | sK8 != X0 ),
% 3.07/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_595,plain,
% 3.07/0.99      ( r2_hidden(sK8,k1_zfmisc_1(sK4)) | v1_xboole_0(k1_zfmisc_1(sK4)) ),
% 3.07/0.99      inference(unflattening,[status(thm)],[c_594]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_601,plain,
% 3.07/0.99      ( r2_hidden(sK8,k1_zfmisc_1(sK4)) ),
% 3.07/0.99      inference(forward_subsumption_resolution,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_595,c_10]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_603,plain,
% 3.07/0.99      ( r2_hidden(sK8,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3059,plain,
% 3.07/0.99      ( r2_hidden(sK8,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_2788,c_603]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3064,plain,
% 3.07/0.99      ( r1_tarski(sK8,sK4) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3059,c_1747]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4182,plain,
% 3.07/0.99      ( r2_hidden(X0,sK8) != iProver_top
% 3.07/0.99      | r2_hidden(X0,sK4) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3064,c_1752]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8153,plain,
% 3.07/0.99      ( r2_hidden(sK0(sK8),sK4) = iProver_top
% 3.07/0.99      | v1_xboole_0(sK8) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1756,c_4182]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4659,plain,
% 3.07/0.99      ( v1_xboole_0(sK8) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_4412,c_1755]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8919,plain,
% 3.07/0.99      ( r2_hidden(sK0(sK8),sK4) = iProver_top ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_8153,c_4659]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8924,plain,
% 3.07/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_8919,c_1755]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8928,plain,
% 3.07/0.99      ( sK3 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_8583,c_8924]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_68,plain,
% 3.07/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_9257,plain,
% 3.07/0.99      ( sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_8928,c_68]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_24,negated_conjecture,
% 3.07/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
% 3.07/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1732,plain,
% 3.07/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2789,plain,
% 3.07/0.99      ( r2_hidden(sK7,k1_zfmisc_1(sK3)) = iProver_top
% 3.07/0.99      | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1732,c_1745]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_604,plain,
% 3.07/0.99      ( r2_hidden(X0,X1)
% 3.07/0.99      | v1_xboole_0(X1)
% 3.07/0.99      | k1_zfmisc_1(sK3) != X1
% 3.07/0.99      | sK7 != X0 ),
% 3.07/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_605,plain,
% 3.07/0.99      ( r2_hidden(sK7,k1_zfmisc_1(sK3)) | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 3.07/0.99      inference(unflattening,[status(thm)],[c_604]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_611,plain,
% 3.07/0.99      ( r2_hidden(sK7,k1_zfmisc_1(sK3)) ),
% 3.07/0.99      inference(forward_subsumption_resolution,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_605,c_10]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_613,plain,
% 3.07/0.99      ( r2_hidden(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3163,plain,
% 3.07/0.99      ( r2_hidden(sK7,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_2789,c_613]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3168,plain,
% 3.07/0.99      ( r1_tarski(sK7,sK3) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3163,c_1747]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4299,plain,
% 3.07/0.99      ( r2_hidden(X0,sK7) != iProver_top
% 3.07/0.99      | r2_hidden(X0,sK3) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3168,c_1752]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8284,plain,
% 3.07/0.99      ( r2_hidden(sK0(sK7),sK3) = iProver_top
% 3.07/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_1756,c_4299]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5456,plain,
% 3.07/0.99      ( v1_xboole_0(sK7) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_4413,c_1755]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_9103,plain,
% 3.07/0.99      ( r2_hidden(sK0(sK7),sK3) = iProver_top ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_8284,c_5456]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_9107,plain,
% 3.07/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_9103,c_1755]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_9259,plain,
% 3.07/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.07/0.99      inference(demodulation,[status(thm)],[c_9257,c_9107]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(contradiction,plain,
% 3.07/0.99      ( $false ),
% 3.07/0.99      inference(minisat,[status(thm)],[c_9259,c_68]) ).
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.07/0.99  
% 3.07/0.99  ------                               Statistics
% 3.07/0.99  
% 3.07/0.99  ------ General
% 3.07/0.99  
% 3.07/0.99  abstr_ref_over_cycles:                  0
% 3.07/0.99  abstr_ref_under_cycles:                 0
% 3.07/0.99  gc_basic_clause_elim:                   0
% 3.07/0.99  forced_gc_time:                         0
% 3.07/0.99  parsing_time:                           0.012
% 3.07/0.99  unif_index_cands_time:                  0.
% 3.07/0.99  unif_index_add_time:                    0.
% 3.07/0.99  orderings_time:                         0.
% 3.07/0.99  out_proof_time:                         0.01
% 3.07/0.99  total_time:                             0.261
% 3.07/0.99  num_of_symbols:                         56
% 3.07/0.99  num_of_terms:                           8897
% 3.07/0.99  
% 3.07/0.99  ------ Preprocessing
% 3.07/0.99  
% 3.07/0.99  num_of_splits:                          0
% 3.07/0.99  num_of_split_atoms:                     0
% 3.07/0.99  num_of_reused_defs:                     0
% 3.07/0.99  num_eq_ax_congr_red:                    12
% 3.07/0.99  num_of_sem_filtered_clauses:            1
% 3.07/0.99  num_of_subtypes:                        0
% 3.07/0.99  monotx_restored_types:                  0
% 3.07/0.99  sat_num_of_epr_types:                   0
% 3.07/0.99  sat_num_of_non_cyclic_types:            0
% 3.07/0.99  sat_guarded_non_collapsed_types:        0
% 3.07/0.99  num_pure_diseq_elim:                    0
% 3.07/0.99  simp_replaced_by:                       0
% 3.07/0.99  res_preprocessed:                       104
% 3.07/0.99  prep_upred:                             0
% 3.07/0.99  prep_unflattend:                        44
% 3.07/0.99  smt_new_axioms:                         0
% 3.07/0.99  pred_elim_cands:                        4
% 3.07/0.99  pred_elim:                              0
% 3.07/0.99  pred_elim_cl:                           0
% 3.07/0.99  pred_elim_cycles:                       3
% 3.07/0.99  merged_defs:                            6
% 3.07/0.99  merged_defs_ncl:                        0
% 3.07/0.99  bin_hyper_res:                          6
% 3.07/0.99  prep_cycles:                            3
% 3.07/0.99  pred_elim_time:                         0.02
% 3.07/0.99  splitting_time:                         0.
% 3.07/0.99  sem_filter_time:                        0.
% 3.07/0.99  monotx_time:                            0.
% 3.07/0.99  subtype_inf_time:                       0.
% 3.07/0.99  
% 3.07/0.99  ------ Problem properties
% 3.07/0.99  
% 3.07/0.99  clauses:                                25
% 3.07/0.99  conjectures:                            7
% 3.07/0.99  epr:                                    4
% 3.07/0.99  horn:                                   17
% 3.07/0.99  ground:                                 8
% 3.07/0.99  unary:                                  8
% 3.07/0.99  binary:                                 8
% 3.07/0.99  lits:                                   64
% 3.07/0.99  lits_eq:                                22
% 3.07/0.99  fd_pure:                                0
% 3.07/0.99  fd_pseudo:                              0
% 3.07/0.99  fd_cond:                                4
% 3.07/0.99  fd_pseudo_cond:                         2
% 3.07/0.99  ac_symbols:                             0
% 3.07/0.99  
% 3.07/0.99  ------ Propositional Solver
% 3.07/0.99  
% 3.07/0.99  prop_solver_calls:                      29
% 3.07/0.99  prop_fast_solver_calls:                 1020
% 3.07/0.99  smt_solver_calls:                       0
% 3.07/0.99  smt_fast_solver_calls:                  0
% 3.07/0.99  prop_num_of_clauses:                    3077
% 3.07/0.99  prop_preprocess_simplified:             8488
% 3.07/0.99  prop_fo_subsumed:                       16
% 3.07/0.99  prop_solver_time:                       0.
% 3.07/0.99  smt_solver_time:                        0.
% 3.07/0.99  smt_fast_solver_time:                   0.
% 3.07/0.99  prop_fast_solver_time:                  0.
% 3.07/0.99  prop_unsat_core_time:                   0.
% 3.07/0.99  
% 3.07/0.99  ------ QBF
% 3.07/0.99  
% 3.07/0.99  qbf_q_res:                              0
% 3.07/0.99  qbf_num_tautologies:                    0
% 3.07/0.99  qbf_prep_cycles:                        0
% 3.07/0.99  
% 3.07/0.99  ------ BMC1
% 3.07/0.99  
% 3.07/0.99  bmc1_current_bound:                     -1
% 3.07/0.99  bmc1_last_solved_bound:                 -1
% 3.07/0.99  bmc1_unsat_core_size:                   -1
% 3.07/0.99  bmc1_unsat_core_parents_size:           -1
% 3.07/0.99  bmc1_merge_next_fun:                    0
% 3.07/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.07/0.99  
% 3.07/0.99  ------ Instantiation
% 3.07/0.99  
% 3.07/0.99  inst_num_of_clauses:                    831
% 3.07/0.99  inst_num_in_passive:                    343
% 3.07/0.99  inst_num_in_active:                     329
% 3.07/0.99  inst_num_in_unprocessed:                159
% 3.07/0.99  inst_num_of_loops:                      460
% 3.07/0.99  inst_num_of_learning_restarts:          0
% 3.07/0.99  inst_num_moves_active_passive:          126
% 3.07/0.99  inst_lit_activity:                      0
% 3.07/0.99  inst_lit_activity_moves:                0
% 3.07/0.99  inst_num_tautologies:                   0
% 3.07/0.99  inst_num_prop_implied:                  0
% 3.07/0.99  inst_num_existing_simplified:           0
% 3.07/0.99  inst_num_eq_res_simplified:             0
% 3.07/0.99  inst_num_child_elim:                    0
% 3.07/0.99  inst_num_of_dismatching_blockings:      640
% 3.07/0.99  inst_num_of_non_proper_insts:           1085
% 3.07/0.99  inst_num_of_duplicates:                 0
% 3.07/0.99  inst_inst_num_from_inst_to_res:         0
% 3.07/0.99  inst_dismatching_checking_time:         0.
% 3.07/0.99  
% 3.07/0.99  ------ Resolution
% 3.07/0.99  
% 3.07/0.99  res_num_of_clauses:                     0
% 3.07/0.99  res_num_in_passive:                     0
% 3.07/0.99  res_num_in_active:                      0
% 3.07/0.99  res_num_of_loops:                       107
% 3.07/0.99  res_forward_subset_subsumed:            36
% 3.07/0.99  res_backward_subset_subsumed:           0
% 3.07/0.99  res_forward_subsumed:                   0
% 3.07/0.99  res_backward_subsumed:                  0
% 3.07/0.99  res_forward_subsumption_resolution:     4
% 3.07/0.99  res_backward_subsumption_resolution:    0
% 3.07/0.99  res_clause_to_clause_subsumption:       288
% 3.07/0.99  res_orphan_elimination:                 0
% 3.07/0.99  res_tautology_del:                      104
% 3.07/0.99  res_num_eq_res_simplified:              0
% 3.07/0.99  res_num_sel_changes:                    0
% 3.07/0.99  res_moves_from_active_to_pass:          0
% 3.07/0.99  
% 3.07/0.99  ------ Superposition
% 3.07/0.99  
% 3.07/0.99  sup_time_total:                         0.
% 3.07/0.99  sup_time_generating:                    0.
% 3.07/0.99  sup_time_sim_full:                      0.
% 3.07/0.99  sup_time_sim_immed:                     0.
% 3.07/0.99  
% 3.07/0.99  sup_num_of_clauses:                     93
% 3.07/0.99  sup_num_in_active:                      58
% 3.07/0.99  sup_num_in_passive:                     35
% 3.07/0.99  sup_num_of_loops:                       90
% 3.07/0.99  sup_fw_superposition:                   49
% 3.07/0.99  sup_bw_superposition:                   105
% 3.07/0.99  sup_immediate_simplified:               11
% 3.07/0.99  sup_given_eliminated:                   0
% 3.07/0.99  comparisons_done:                       0
% 3.07/0.99  comparisons_avoided:                    60
% 3.07/0.99  
% 3.07/0.99  ------ Simplifications
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  sim_fw_subset_subsumed:                 3
% 3.07/0.99  sim_bw_subset_subsumed:                 41
% 3.07/0.99  sim_fw_subsumed:                        8
% 3.07/0.99  sim_bw_subsumed:                        9
% 3.07/0.99  sim_fw_subsumption_res:                 0
% 3.07/0.99  sim_bw_subsumption_res:                 0
% 3.07/0.99  sim_tautology_del:                      5
% 3.07/0.99  sim_eq_tautology_del:                   8
% 3.07/0.99  sim_eq_res_simp:                        0
% 3.07/0.99  sim_fw_demodulated:                     0
% 3.07/0.99  sim_bw_demodulated:                     11
% 3.07/0.99  sim_light_normalised:                   0
% 3.07/0.99  sim_joinable_taut:                      0
% 3.07/0.99  sim_joinable_simp:                      0
% 3.07/0.99  sim_ac_normalised:                      0
% 3.07/0.99  sim_smt_subsumption:                    0
% 3.07/0.99  
%------------------------------------------------------------------------------
