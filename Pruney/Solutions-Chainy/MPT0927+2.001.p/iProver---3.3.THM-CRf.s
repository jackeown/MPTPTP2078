%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:30 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  143 (1251 expanded)
%              Number of clauses        :   94 ( 419 expanded)
%              Number of leaves         :   17 ( 408 expanded)
%              Depth                    :   19
%              Number of atoms          :  516 (6859 expanded)
%              Number of equality atoms :  256 ( 778 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f13])).

fof(f23,plain,(
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

fof(f22,plain,(
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

fof(f21,plain,(
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

fof(f20,plain,(
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

fof(f19,plain,
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

fof(f24,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f14,f23,f22,f21,f20,f19])).

fof(f41,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f50,plain,(
    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f41,f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f42,plain,(
    r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f25,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f43,plain,
    ( ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8)
    | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
    | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
    | ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f44])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1131,plain,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1136,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3951,plain,
    ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(sK9))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1131,c_1136])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_200,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_201,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK8)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_203,plain,
    ( v1_xboole_0(sK8)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_215,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_216,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK7)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_218,plain,
    ( v1_xboole_0(sK7)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_230,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_231,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_233,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK2) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_245,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_246,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_248,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_816,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_841,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1280,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK8)
    | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1283,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
    | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1338,plain,
    ( ~ r2_hidden(k2_mcart_1(sK9),sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1354,plain,
    ( ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1353,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
    | ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1559,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
    | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1558,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1565,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_820,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1653,plain,
    ( X0 != sK4
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1658,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK4)
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_1814,plain,
    ( X0 != sK3
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1819,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK3)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1814])).

cnf(c_1844,plain,
    ( X0 != sK2
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK2) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1849,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK2)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1844])).

cnf(c_1874,plain,
    ( X0 != sK1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1879,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK1)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1874])).

cnf(c_3070,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3078,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_817,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3557,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_3558,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3557])).

cnf(c_3728,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_3729,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3728])).

cnf(c_3785,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_3786,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3785])).

cnf(c_3806,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_3807,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3806])).

cnf(c_6275,plain,
    ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3951,c_11,c_2,c_203,c_218,c_233,c_248,c_841,c_1280,c_1283,c_1338,c_1354,c_1353,c_1559,c_1558,c_1565,c_1658,c_1819,c_1849,c_1879,c_3070,c_3078,c_3558,c_3729,c_3786,c_3807])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1137,plain,
    ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3765,plain,
    ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(sK9)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1131,c_1137])).

cnf(c_5101,plain,
    ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3765,c_11,c_2,c_203,c_218,c_233,c_248,c_841,c_1280,c_1283,c_1338,c_1354,c_1353,c_1559,c_1558,c_1565,c_1658,c_1819,c_1849,c_1879,c_3070,c_3078,c_3558,c_3729,c_3786,c_3807])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)
    | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
    | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
    | ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1133,plain,
    ( r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) != iProver_top
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5105,plain,
    ( r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) != iProver_top
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5101,c_1133])).

cnf(c_22,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1281,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK8) = iProver_top
    | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1280])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1134,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1600,plain,
    ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1131,c_1134])).

cnf(c_2798,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_1133])).

cnf(c_1284,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top
    | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1283])).

cnf(c_1357,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1353])).

cnf(c_1562,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) = iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_2801,plain,
    ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2798,c_22,c_1284,c_1357,c_1562])).

cnf(c_2802,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_2801])).

cnf(c_5104,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5101,c_2802])).

cnf(c_5131,plain,
    ( r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
    | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5105,c_11,c_22,c_2,c_203,c_218,c_233,c_248,c_841,c_1280,c_1281,c_1283,c_1338,c_1354,c_1353,c_1559,c_1558,c_1565,c_1658,c_1819,c_1849,c_1879,c_3070,c_3078,c_3558,c_3729,c_3786,c_3807,c_5104])).

cnf(c_5132,plain,
    ( r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5131])).

cnf(c_6278,plain,
    ( r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6275,c_5132])).

cnf(c_1355,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1354])).

cnf(c_9339,plain,
    ( r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6278,c_22,c_1284,c_1355])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1135,plain,
    ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3528,plain,
    ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1131,c_1135])).

cnf(c_6280,plain,
    ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3528,c_11,c_2,c_203,c_218,c_233,c_248,c_841,c_1280,c_1283,c_1338,c_1354,c_1353,c_1559,c_1558,c_1565,c_1658,c_1819,c_1849,c_1879,c_3070,c_3078,c_3558,c_3729,c_3786,c_3807])).

cnf(c_9343,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9339,c_6280])).

cnf(c_1132,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1138,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1779,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1138])).

cnf(c_2361,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_1138])).

cnf(c_1139,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7269,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2361,c_1139])).

cnf(c_9345,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9343,c_7269])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.03/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.03/0.99  
% 2.03/0.99  ------  iProver source info
% 2.03/0.99  
% 2.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.03/0.99  git: non_committed_changes: false
% 2.03/0.99  git: last_make_outside_of_git: false
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     num_symb
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       true
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/0.99  --sup_to_prop_solver                    passive
% 2.03/0.99  --sup_prop_simpl_new                    true
% 2.03/0.99  --sup_prop_simpl_given                  true
% 2.03/0.99  --sup_fun_splitting                     false
% 2.03/0.99  --sup_smt_interval                      50000
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Simplification Setup
% 2.03/0.99  
% 2.03/0.99  --sup_indices_passive                   []
% 2.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_full_bw                           [BwDemod]
% 2.03/0.99  --sup_immed_triv                        [TrivRules]
% 2.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_immed_bw_main                     []
% 2.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  
% 2.03/0.99  ------ Combination Options
% 2.03/0.99  
% 2.03/0.99  --comb_res_mult                         3
% 2.03/0.99  --comb_sup_mult                         2
% 2.03/0.99  --comb_inst_mult                        10
% 2.03/0.99  
% 2.03/0.99  ------ Debug Options
% 2.03/0.99  
% 2.03/0.99  --dbg_backtrace                         false
% 2.03/0.99  --dbg_dump_prop_clauses                 false
% 2.03/0.99  --dbg_dump_prop_clauses_file            -
% 2.03/0.99  --dbg_out_stat                          false
% 2.03/0.99  ------ Parsing...
% 2.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.03/0.99  ------ Proving...
% 2.03/0.99  ------ Problem Properties 
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  clauses                                 17
% 2.03/0.99  conjectures                             7
% 2.03/0.99  EPR                                     2
% 2.03/0.99  Horn                                    12
% 2.03/0.99  unary                                   7
% 2.03/0.99  binary                                  4
% 2.03/0.99  lits                                    46
% 2.03/0.99  lits eq                                 20
% 2.03/0.99  fd_pure                                 0
% 2.03/0.99  fd_pseudo                               0
% 2.03/0.99  fd_cond                                 4
% 2.03/0.99  fd_pseudo_cond                          0
% 2.03/0.99  AC symbols                              0
% 2.03/0.99  
% 2.03/0.99  ------ Schedule dynamic 5 is on 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  Current options:
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     none
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       false
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/0.99  --sup_to_prop_solver                    passive
% 2.03/0.99  --sup_prop_simpl_new                    true
% 2.03/0.99  --sup_prop_simpl_given                  true
% 2.03/0.99  --sup_fun_splitting                     false
% 2.03/0.99  --sup_smt_interval                      50000
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Simplification Setup
% 2.03/0.99  
% 2.03/0.99  --sup_indices_passive                   []
% 2.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_full_bw                           [BwDemod]
% 2.03/0.99  --sup_immed_triv                        [TrivRules]
% 2.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_immed_bw_main                     []
% 2.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  
% 2.03/0.99  ------ Combination Options
% 2.03/0.99  
% 2.03/0.99  --comb_res_mult                         3
% 2.03/0.99  --comb_sup_mult                         2
% 2.03/0.99  --comb_inst_mult                        10
% 2.03/0.99  
% 2.03/0.99  ------ Debug Options
% 2.03/0.99  
% 2.03/0.99  --dbg_backtrace                         false
% 2.03/0.99  --dbg_dump_prop_clauses                 false
% 2.03/0.99  --dbg_dump_prop_clauses_file            -
% 2.03/0.99  --dbg_out_stat                          false
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  ------ Proving...
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  % SZS status Theorem for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99   Resolution empty clause
% 2.03/0.99  
% 2.03/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  fof(f8,conjecture,(
% 2.03/0.99    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 2.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f9,negated_conjecture,(
% 2.03/0.99    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 2.03/0.99    inference(negated_conjecture,[],[f8])).
% 2.03/0.99  
% 2.03/0.99  fof(f13,plain,(
% 2.03/0.99    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f9])).
% 2.03/0.99  
% 2.03/0.99  fof(f14,plain,(
% 2.03/0.99    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 2.03/0.99    inference(flattening,[],[f13])).
% 2.03/0.99  
% 2.03/0.99  fof(f23,plain,(
% 2.03/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) => ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,sK9),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,sK9),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,sK9),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,sK9),X4)) & r2_hidden(sK9,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(sK9,k4_zfmisc_1(X0,X1,X2,X3)))) )),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f22,plain,(
% 2.03/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),sK8) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,sK8)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(sK8,k1_zfmisc_1(X3)))) )),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f21,plain,(
% 2.03/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),sK7) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,sK7,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(sK7,k1_zfmisc_1(X2)))) )),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f20,plain,(
% 2.03/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),sK6) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,sK6,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(sK6,k1_zfmisc_1(X1)))) )),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f19,plain,(
% 2.03/0.99    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,X8),X7) | ~r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,X8),X6) | ~r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,X8),X5) | ~r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,X8),sK5)) & r2_hidden(X8,k4_zfmisc_1(sK5,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK1,sK2,sK3,sK4))) & m1_subset_1(X7,k1_zfmisc_1(sK4))) & m1_subset_1(X6,k1_zfmisc_1(sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1)))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f24,plain,(
% 2.03/0.99    (((((~r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) | ~r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) | ~r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) | ~r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)) & r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) & m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4))) & m1_subset_1(sK8,k1_zfmisc_1(sK4))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f14,f23,f22,f21,f20,f19])).
% 2.03/0.99  
% 2.03/0.99  fof(f41,plain,(
% 2.03/0.99    m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 2.03/0.99    inference(cnf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f5,axiom,(
% 2.03/0.99    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 2.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f30,plain,(
% 2.03/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f5])).
% 2.03/0.99  
% 2.03/0.99  fof(f4,axiom,(
% 2.03/0.99    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f29,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f4])).
% 2.03/0.99  
% 2.03/0.99  fof(f44,plain,(
% 2.03/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f30,f29])).
% 2.03/0.99  
% 2.03/0.99  fof(f50,plain,(
% 2.03/0.99    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 2.03/0.99    inference(definition_unfolding,[],[f41,f44])).
% 2.03/0.99  
% 2.03/0.99  fof(f7,axiom,(
% 2.03/0.99    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f12,plain,(
% 2.03/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) & k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) & k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.03/0.99    inference(ennf_transformation,[],[f7])).
% 2.03/0.99  
% 2.03/0.99  fof(f35,plain,(
% 2.03/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.03/0.99    inference(cnf_transformation,[],[f12])).
% 2.03/0.99  
% 2.03/0.99  fof(f46,plain,(
% 2.03/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.03/0.99    inference(definition_unfolding,[],[f35,f44])).
% 2.03/0.99  
% 2.03/0.99  fof(f42,plain,(
% 2.03/0.99    r2_hidden(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8))),
% 2.03/0.99    inference(cnf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f49,plain,(
% 2.03/0.99    r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8))),
% 2.03/0.99    inference(definition_unfolding,[],[f42,f44])).
% 2.03/0.99  
% 2.03/0.99  fof(f2,axiom,(
% 2.03/0.99    v1_xboole_0(k1_xboole_0)),
% 2.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f27,plain,(
% 2.03/0.99    v1_xboole_0(k1_xboole_0)),
% 2.03/0.99    inference(cnf_transformation,[],[f2])).
% 2.03/0.99  
% 2.03/0.99  fof(f3,axiom,(
% 2.03/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f10,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f3])).
% 2.03/0.99  
% 2.03/0.99  fof(f28,plain,(
% 2.03/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f10])).
% 2.03/0.99  
% 2.03/0.99  fof(f40,plain,(
% 2.03/0.99    m1_subset_1(sK8,k1_zfmisc_1(sK4))),
% 2.03/0.99    inference(cnf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f39,plain,(
% 2.03/0.99    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 2.03/0.99    inference(cnf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f38,plain,(
% 2.03/0.99    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 2.03/0.99    inference(cnf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f37,plain,(
% 2.03/0.99    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 2.03/0.99    inference(cnf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f6,axiom,(
% 2.03/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f11,plain,(
% 2.03/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.03/0.99    inference(ennf_transformation,[],[f6])).
% 2.03/0.99  
% 2.03/0.99  fof(f32,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f11])).
% 2.03/0.99  
% 2.03/0.99  fof(f31,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f11])).
% 2.03/0.99  
% 2.03/0.99  fof(f1,axiom,(
% 2.03/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f15,plain,(
% 2.03/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.03/0.99    inference(nnf_transformation,[],[f1])).
% 2.03/0.99  
% 2.03/0.99  fof(f16,plain,(
% 2.03/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.03/0.99    inference(rectify,[],[f15])).
% 2.03/0.99  
% 2.03/0.99  fof(f17,plain,(
% 2.03/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f18,plain,(
% 2.03/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 2.03/0.99  
% 2.03/0.99  fof(f25,plain,(
% 2.03/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f18])).
% 2.03/0.99  
% 2.03/0.99  fof(f36,plain,(
% 2.03/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.03/0.99    inference(cnf_transformation,[],[f12])).
% 2.03/0.99  
% 2.03/0.99  fof(f45,plain,(
% 2.03/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.03/0.99    inference(definition_unfolding,[],[f36,f44])).
% 2.03/0.99  
% 2.03/0.99  fof(f43,plain,(
% 2.03/0.99    ~r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) | ~r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) | ~r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) | ~r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)),
% 2.03/0.99    inference(cnf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f33,plain,(
% 2.03/0.99    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.03/0.99    inference(cnf_transformation,[],[f12])).
% 2.03/0.99  
% 2.03/0.99  fof(f48,plain,(
% 2.03/0.99    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k8_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.03/0.99    inference(definition_unfolding,[],[f33,f44])).
% 2.03/0.99  
% 2.03/0.99  fof(f34,plain,(
% 2.03/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.03/0.99    inference(cnf_transformation,[],[f12])).
% 2.03/0.99  
% 2.03/0.99  fof(f47,plain,(
% 2.03/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) = k9_mcart_1(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.03/0.99    inference(definition_unfolding,[],[f34,f44])).
% 2.03/0.99  
% 2.03/0.99  cnf(c_12,negated_conjecture,
% 2.03/0.99      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1131,plain,
% 2.03/0.99      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_7,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.03/0.99      | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.03/0.99      | k1_xboole_0 = X4
% 2.03/0.99      | k1_xboole_0 = X3
% 2.03/0.99      | k1_xboole_0 = X2
% 2.03/0.99      | k1_xboole_0 = X1 ),
% 2.03/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1136,plain,
% 2.03/0.99      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
% 2.03/0.99      | k1_xboole_0 = X3
% 2.03/0.99      | k1_xboole_0 = X0
% 2.03/0.99      | k1_xboole_0 = X1
% 2.03/0.99      | k1_xboole_0 = X2
% 2.03/0.99      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3951,plain,
% 2.03/0.99      ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(sK9))
% 2.03/0.99      | sK4 = k1_xboole_0
% 2.03/0.99      | sK3 = k1_xboole_0
% 2.03/0.99      | sK2 = k1_xboole_0
% 2.03/0.99      | sK1 = k1_xboole_0 ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1131,c_1136]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_11,negated_conjecture,
% 2.03/0.99      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2,plain,
% 2.03/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f27]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.03/0.99      | ~ v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_13,negated_conjecture,
% 2.03/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(sK4)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_200,plain,
% 2.03/0.99      ( ~ v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4)
% 2.03/0.99      | sK8 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_201,plain,
% 2.03/0.99      ( ~ v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(sK8)
% 2.03/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK4) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_200]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_203,plain,
% 2.03/0.99      ( v1_xboole_0(sK8)
% 2.03/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.03/0.99      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK4) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_201]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_14,negated_conjecture,
% 2.03/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_215,plain,
% 2.03/0.99      ( ~ v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3)
% 2.03/0.99      | sK7 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_216,plain,
% 2.03/0.99      ( ~ v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(sK7)
% 2.03/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_215]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_218,plain,
% 2.03/0.99      ( v1_xboole_0(sK7)
% 2.03/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.03/0.99      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK3) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_216]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_15,negated_conjecture,
% 2.03/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_230,plain,
% 2.03/0.99      ( ~ v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
% 2.03/0.99      | sK6 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_231,plain,
% 2.03/0.99      ( ~ v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(sK6)
% 2.03/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_230]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_233,plain,
% 2.03/0.99      ( v1_xboole_0(sK6)
% 2.03/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.03/0.99      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK2) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_231]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_16,negated_conjecture,
% 2.03/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_245,plain,
% 2.03/0.99      ( ~ v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 2.03/0.99      | sK5 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_246,plain,
% 2.03/0.99      ( ~ v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(sK5)
% 2.03/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_245]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_248,plain,
% 2.03/0.99      ( v1_xboole_0(sK5)
% 2.03/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.03/0.99      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK1) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_246]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_816,plain,( X0 = X0 ),theory(equality) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_841,plain,
% 2.03/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_816]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_4,plain,
% 2.03/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.03/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1280,plain,
% 2.03/0.99      ( r2_hidden(k2_mcart_1(sK9),sK8)
% 2.03/0.99      | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_5,plain,
% 2.03/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1283,plain,
% 2.03/0.99      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
% 2.03/0.99      | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1,plain,
% 2.03/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f25]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1338,plain,
% 2.03/0.99      ( ~ r2_hidden(k2_mcart_1(sK9),sK8) | ~ v1_xboole_0(sK8) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1354,plain,
% 2.03/0.99      ( ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))
% 2.03/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1353,plain,
% 2.03/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
% 2.03/0.99      | ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1559,plain,
% 2.03/0.99      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6))
% 2.03/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1558,plain,
% 2.03/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5)
% 2.03/0.99      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1565,plain,
% 2.03/0.99      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) | ~ v1_xboole_0(sK7) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_820,plain,
% 2.03/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.03/0.99      theory(equality) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1653,plain,
% 2.03/0.99      ( X0 != sK4 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK4) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_820]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1658,plain,
% 2.03/0.99      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK4) | k1_xboole_0 != sK4 ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_1653]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1814,plain,
% 2.03/0.99      ( X0 != sK3 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_820]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1819,plain,
% 2.03/0.99      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK3) | k1_xboole_0 != sK3 ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_1814]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1844,plain,
% 2.03/0.99      ( X0 != sK2 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK2) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_820]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1849,plain,
% 2.03/0.99      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK2) | k1_xboole_0 != sK2 ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_1844]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1874,plain,
% 2.03/0.99      ( X0 != sK1 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK1) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_820]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1879,plain,
% 2.03/1.00      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK1) | k1_xboole_0 != sK1 ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_1874]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3070,plain,
% 2.03/1.00      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5)
% 2.03/1.00      | ~ v1_xboole_0(sK5) ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3078,plain,
% 2.03/1.00      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6)
% 2.03/1.00      | ~ v1_xboole_0(sK6) ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_817,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3557,plain,
% 2.03/1.00      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_817]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3558,plain,
% 2.03/1.00      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_3557]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3728,plain,
% 2.03/1.00      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_817]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3729,plain,
% 2.03/1.00      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_3728]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3785,plain,
% 2.03/1.00      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_817]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3786,plain,
% 2.03/1.00      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_3785]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3806,plain,
% 2.03/1.00      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_817]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3807,plain,
% 2.03/1.00      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_3806]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_6275,plain,
% 2.03/1.00      ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(sK9)) ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_3951,c_11,c_2,c_203,c_218,c_233,c_248,c_841,c_1280,c_1283,
% 2.03/1.00                 c_1338,c_1354,c_1353,c_1559,c_1558,c_1565,c_1658,c_1819,
% 2.03/1.00                 c_1849,c_1879,c_3070,c_3078,c_3558,c_3729,c_3786,c_3807]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_6,plain,
% 2.03/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.03/1.00      | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
% 2.03/1.00      | k1_xboole_0 = X4
% 2.03/1.00      | k1_xboole_0 = X3
% 2.03/1.00      | k1_xboole_0 = X2
% 2.03/1.00      | k1_xboole_0 = X1 ),
% 2.03/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1137,plain,
% 2.03/1.00      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
% 2.03/1.00      | k1_xboole_0 = X3
% 2.03/1.00      | k1_xboole_0 = X0
% 2.03/1.00      | k1_xboole_0 = X1
% 2.03/1.00      | k1_xboole_0 = X2
% 2.03/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3765,plain,
% 2.03/1.00      ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(sK9)
% 2.03/1.00      | sK4 = k1_xboole_0
% 2.03/1.00      | sK3 = k1_xboole_0
% 2.03/1.00      | sK2 = k1_xboole_0
% 2.03/1.00      | sK1 = k1_xboole_0 ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_1131,c_1137]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_5101,plain,
% 2.03/1.00      ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(sK9) ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_3765,c_11,c_2,c_203,c_218,c_233,c_248,c_841,c_1280,c_1283,
% 2.03/1.00                 c_1338,c_1354,c_1353,c_1559,c_1558,c_1565,c_1658,c_1819,
% 2.03/1.00                 c_1849,c_1879,c_3070,c_3078,c_3558,c_3729,c_3786,c_3807]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_10,negated_conjecture,
% 2.03/1.00      ( ~ r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5)
% 2.03/1.00      | ~ r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6)
% 2.03/1.00      | ~ r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7)
% 2.03/1.00      | ~ r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) ),
% 2.03/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1133,plain,
% 2.03/1.00      ( r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) != iProver_top
% 2.03/1.00      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 2.03/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 2.03/1.00      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_5105,plain,
% 2.03/1.00      ( r2_hidden(k8_mcart_1(sK1,sK2,sK3,sK4,sK9),sK5) != iProver_top
% 2.03/1.00      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 2.03/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 2.03/1.00      | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top ),
% 2.03/1.00      inference(demodulation,[status(thm)],[c_5101,c_1133]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_22,plain,
% 2.03/1.00      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1281,plain,
% 2.03/1.00      ( r2_hidden(k2_mcart_1(sK9),sK8) = iProver_top
% 2.03/1.00      | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1280]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_9,plain,
% 2.03/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.03/1.00      | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 2.03/1.00      | k1_xboole_0 = X4
% 2.03/1.00      | k1_xboole_0 = X3
% 2.03/1.00      | k1_xboole_0 = X2
% 2.03/1.00      | k1_xboole_0 = X1 ),
% 2.03/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1134,plain,
% 2.03/1.00      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 2.03/1.00      | k1_xboole_0 = X3
% 2.03/1.00      | k1_xboole_0 = X0
% 2.03/1.00      | k1_xboole_0 = X1
% 2.03/1.00      | k1_xboole_0 = X2
% 2.03/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1600,plain,
% 2.03/1.00      ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 2.03/1.00      | sK4 = k1_xboole_0
% 2.03/1.00      | sK3 = k1_xboole_0
% 2.03/1.00      | sK2 = k1_xboole_0
% 2.03/1.00      | sK1 = k1_xboole_0 ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_1131,c_1134]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2798,plain,
% 2.03/1.00      ( sK4 = k1_xboole_0
% 2.03/1.00      | sK3 = k1_xboole_0
% 2.03/1.00      | sK2 = k1_xboole_0
% 2.03/1.00      | sK1 = k1_xboole_0
% 2.03/1.00      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 2.03/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 2.03/1.00      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 2.03/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) != iProver_top ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_1600,c_1133]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1284,plain,
% 2.03/1.00      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top
% 2.03/1.00      | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1283]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1357,plain,
% 2.03/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top
% 2.03/1.00      | r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1353]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1562,plain,
% 2.03/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK5) = iProver_top
% 2.03/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1558]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2801,plain,
% 2.03/1.00      ( r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top
% 2.03/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 2.03/1.00      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 2.03/1.00      | sK1 = k1_xboole_0
% 2.03/1.00      | sK2 = k1_xboole_0
% 2.03/1.00      | sK3 = k1_xboole_0
% 2.03/1.00      | sK4 = k1_xboole_0 ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_2798,c_22,c_1284,c_1357,c_1562]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2802,plain,
% 2.03/1.00      ( sK4 = k1_xboole_0
% 2.03/1.00      | sK3 = k1_xboole_0
% 2.03/1.00      | sK2 = k1_xboole_0
% 2.03/1.00      | sK1 = k1_xboole_0
% 2.03/1.00      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 2.03/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 2.03/1.00      | r2_hidden(k11_mcart_1(sK1,sK2,sK3,sK4,sK9),sK8) != iProver_top ),
% 2.03/1.00      inference(renaming,[status(thm)],[c_2801]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_5104,plain,
% 2.03/1.00      ( sK4 = k1_xboole_0
% 2.03/1.00      | sK3 = k1_xboole_0
% 2.03/1.00      | sK2 = k1_xboole_0
% 2.03/1.00      | sK1 = k1_xboole_0
% 2.03/1.00      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 2.03/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 2.03/1.00      | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top ),
% 2.03/1.00      inference(demodulation,[status(thm)],[c_5101,c_2802]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_5131,plain,
% 2.03/1.00      ( r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top
% 2.03/1.00      | r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_5105,c_11,c_22,c_2,c_203,c_218,c_233,c_248,c_841,c_1280,
% 2.03/1.00                 c_1281,c_1283,c_1338,c_1354,c_1353,c_1559,c_1558,c_1565,
% 2.03/1.00                 c_1658,c_1819,c_1849,c_1879,c_3070,c_3078,c_3558,c_3729,
% 2.03/1.00                 c_3786,c_3807,c_5104]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_5132,plain,
% 2.03/1.00      ( r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 2.03/1.00      | r2_hidden(k10_mcart_1(sK1,sK2,sK3,sK4,sK9),sK7) != iProver_top ),
% 2.03/1.00      inference(renaming,[status(thm)],[c_5131]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_6278,plain,
% 2.03/1.00      ( r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top
% 2.03/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top ),
% 2.03/1.00      inference(demodulation,[status(thm)],[c_6275,c_5132]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1355,plain,
% 2.03/1.00      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top
% 2.03/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1354]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_9339,plain,
% 2.03/1.00      ( r2_hidden(k9_mcart_1(sK1,sK2,sK3,sK4,sK9),sK6) != iProver_top ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_6278,c_22,c_1284,c_1355]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_8,plain,
% 2.03/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.03/1.00      | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 2.03/1.00      | k1_xboole_0 = X4
% 2.03/1.00      | k1_xboole_0 = X3
% 2.03/1.00      | k1_xboole_0 = X2
% 2.03/1.00      | k1_xboole_0 = X1 ),
% 2.03/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1135,plain,
% 2.03/1.00      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 2.03/1.00      | k1_xboole_0 = X3
% 2.03/1.00      | k1_xboole_0 = X0
% 2.03/1.00      | k1_xboole_0 = X1
% 2.03/1.00      | k1_xboole_0 = X2
% 2.03/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3528,plain,
% 2.03/1.00      ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
% 2.03/1.00      | sK4 = k1_xboole_0
% 2.03/1.00      | sK3 = k1_xboole_0
% 2.03/1.00      | sK2 = k1_xboole_0
% 2.03/1.00      | sK1 = k1_xboole_0 ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_1131,c_1135]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_6280,plain,
% 2.03/1.00      ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_3528,c_11,c_2,c_203,c_218,c_233,c_248,c_841,c_1280,c_1283,
% 2.03/1.00                 c_1338,c_1354,c_1353,c_1559,c_1558,c_1565,c_1658,c_1819,
% 2.03/1.00                 c_1849,c_1879,c_3070,c_3078,c_3558,c_3729,c_3786,c_3807]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_9343,plain,
% 2.03/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) != iProver_top ),
% 2.03/1.00      inference(light_normalisation,[status(thm)],[c_9339,c_6280]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1132,plain,
% 2.03/1.00      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7),sK8)) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1138,plain,
% 2.03/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.03/1.00      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1779,plain,
% 2.03/1.00      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_1132,c_1138]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2361,plain,
% 2.03/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_1779,c_1138]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1139,plain,
% 2.03/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.03/1.00      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_7269,plain,
% 2.03/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))),sK6) = iProver_top ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_2361,c_1139]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_9345,plain,
% 2.03/1.00      ( $false ),
% 2.03/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_9343,c_7269]) ).
% 2.03/1.00  
% 2.03/1.00  
% 2.03/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.03/1.00  
% 2.03/1.00  ------                               Statistics
% 2.03/1.00  
% 2.03/1.00  ------ General
% 2.03/1.00  
% 2.03/1.00  abstr_ref_over_cycles:                  0
% 2.03/1.00  abstr_ref_under_cycles:                 0
% 2.03/1.00  gc_basic_clause_elim:                   0
% 2.03/1.00  forced_gc_time:                         0
% 2.03/1.00  parsing_time:                           0.007
% 2.03/1.00  unif_index_cands_time:                  0.
% 2.03/1.00  unif_index_add_time:                    0.
% 2.03/1.00  orderings_time:                         0.
% 2.03/1.00  out_proof_time:                         0.011
% 2.03/1.00  total_time:                             0.257
% 2.03/1.00  num_of_symbols:                         53
% 2.03/1.00  num_of_terms:                           15758
% 2.03/1.00  
% 2.03/1.00  ------ Preprocessing
% 2.03/1.00  
% 2.03/1.00  num_of_splits:                          0
% 2.03/1.00  num_of_split_atoms:                     0
% 2.03/1.00  num_of_reused_defs:                     0
% 2.03/1.00  num_eq_ax_congr_red:                    2
% 2.03/1.00  num_of_sem_filtered_clauses:            1
% 2.03/1.00  num_of_subtypes:                        0
% 2.03/1.00  monotx_restored_types:                  0
% 2.03/1.00  sat_num_of_epr_types:                   0
% 2.03/1.00  sat_num_of_non_cyclic_types:            0
% 2.03/1.00  sat_guarded_non_collapsed_types:        0
% 2.03/1.00  num_pure_diseq_elim:                    0
% 2.03/1.00  simp_replaced_by:                       0
% 2.03/1.00  res_preprocessed:                       78
% 2.03/1.00  prep_upred:                             0
% 2.03/1.00  prep_unflattend:                        25
% 2.03/1.00  smt_new_axioms:                         0
% 2.03/1.00  pred_elim_cands:                        3
% 2.03/1.00  pred_elim:                              0
% 2.03/1.00  pred_elim_cl:                           0
% 2.03/1.00  pred_elim_cycles:                       1
% 2.03/1.00  merged_defs:                            0
% 2.03/1.00  merged_defs_ncl:                        0
% 2.03/1.00  bin_hyper_res:                          0
% 2.03/1.00  prep_cycles:                            3
% 2.03/1.00  pred_elim_time:                         0.007
% 2.03/1.00  splitting_time:                         0.
% 2.03/1.00  sem_filter_time:                        0.
% 2.03/1.00  monotx_time:                            0.
% 2.03/1.00  subtype_inf_time:                       0.
% 2.03/1.00  
% 2.03/1.00  ------ Problem properties
% 2.03/1.00  
% 2.03/1.00  clauses:                                17
% 2.03/1.00  conjectures:                            7
% 2.03/1.00  epr:                                    2
% 2.03/1.00  horn:                                   12
% 2.03/1.00  ground:                                 8
% 2.03/1.00  unary:                                  7
% 2.03/1.00  binary:                                 4
% 2.03/1.00  lits:                                   46
% 2.03/1.00  lits_eq:                                20
% 2.03/1.00  fd_pure:                                0
% 2.03/1.00  fd_pseudo:                              0
% 2.03/1.00  fd_cond:                                4
% 2.03/1.00  fd_pseudo_cond:                         0
% 2.03/1.00  ac_symbols:                             0
% 2.03/1.00  
% 2.03/1.00  ------ Propositional Solver
% 2.03/1.00  
% 2.03/1.00  prop_solver_calls:                      25
% 2.03/1.00  prop_fast_solver_calls:                 723
% 2.03/1.00  smt_solver_calls:                       0
% 2.03/1.00  smt_fast_solver_calls:                  0
% 2.03/1.00  prop_num_of_clauses:                    2770
% 2.03/1.00  prop_preprocess_simplified:             11543
% 2.03/1.00  prop_fo_subsumed:                       20
% 2.03/1.00  prop_solver_time:                       0.
% 2.03/1.00  smt_solver_time:                        0.
% 2.03/1.00  smt_fast_solver_time:                   0.
% 2.03/1.00  prop_fast_solver_time:                  0.
% 2.03/1.00  prop_unsat_core_time:                   0.
% 2.03/1.00  
% 2.03/1.00  ------ QBF
% 2.03/1.00  
% 2.03/1.00  qbf_q_res:                              0
% 2.03/1.00  qbf_num_tautologies:                    0
% 2.03/1.00  qbf_prep_cycles:                        0
% 2.03/1.00  
% 2.03/1.00  ------ BMC1
% 2.03/1.00  
% 2.03/1.00  bmc1_current_bound:                     -1
% 2.03/1.00  bmc1_last_solved_bound:                 -1
% 2.03/1.00  bmc1_unsat_core_size:                   -1
% 2.03/1.00  bmc1_unsat_core_parents_size:           -1
% 2.03/1.00  bmc1_merge_next_fun:                    0
% 2.03/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.03/1.00  
% 2.03/1.00  ------ Instantiation
% 2.03/1.00  
% 2.03/1.00  inst_num_of_clauses:                    1123
% 2.03/1.00  inst_num_in_passive:                    921
% 2.03/1.00  inst_num_in_active:                     199
% 2.03/1.00  inst_num_in_unprocessed:                3
% 2.03/1.00  inst_num_of_loops:                      200
% 2.03/1.00  inst_num_of_learning_restarts:          0
% 2.03/1.00  inst_num_moves_active_passive:          0
% 2.03/1.00  inst_lit_activity:                      0
% 2.03/1.00  inst_lit_activity_moves:                0
% 2.03/1.00  inst_num_tautologies:                   0
% 2.03/1.00  inst_num_prop_implied:                  0
% 2.03/1.00  inst_num_existing_simplified:           0
% 2.03/1.00  inst_num_eq_res_simplified:             0
% 2.03/1.00  inst_num_child_elim:                    0
% 2.03/1.00  inst_num_of_dismatching_blockings:      23
% 2.03/1.00  inst_num_of_non_proper_insts:           784
% 2.03/1.00  inst_num_of_duplicates:                 0
% 2.03/1.00  inst_inst_num_from_inst_to_res:         0
% 2.03/1.00  inst_dismatching_checking_time:         0.
% 2.03/1.00  
% 2.03/1.00  ------ Resolution
% 2.03/1.00  
% 2.03/1.00  res_num_of_clauses:                     0
% 2.03/1.00  res_num_in_passive:                     0
% 2.03/1.00  res_num_in_active:                      0
% 2.03/1.00  res_num_of_loops:                       81
% 2.03/1.00  res_forward_subset_subsumed:            22
% 2.03/1.00  res_backward_subset_subsumed:           0
% 2.03/1.00  res_forward_subsumed:                   0
% 2.03/1.00  res_backward_subsumed:                  0
% 2.03/1.00  res_forward_subsumption_resolution:     0
% 2.03/1.00  res_backward_subsumption_resolution:    0
% 2.03/1.00  res_clause_to_clause_subsumption:       38
% 2.03/1.00  res_orphan_elimination:                 0
% 2.03/1.00  res_tautology_del:                      27
% 2.03/1.00  res_num_eq_res_simplified:              0
% 2.03/1.00  res_num_sel_changes:                    0
% 2.03/1.00  res_moves_from_active_to_pass:          0
% 2.03/1.00  
% 2.03/1.00  ------ Superposition
% 2.03/1.00  
% 2.03/1.00  sup_time_total:                         0.
% 2.03/1.00  sup_time_generating:                    0.
% 2.03/1.00  sup_time_sim_full:                      0.
% 2.03/1.00  sup_time_sim_immed:                     0.
% 2.03/1.00  
% 2.03/1.00  sup_num_of_clauses:                     42
% 2.03/1.00  sup_num_in_active:                      36
% 2.03/1.00  sup_num_in_passive:                     6
% 2.03/1.00  sup_num_of_loops:                       39
% 2.03/1.00  sup_fw_superposition:                   14
% 2.03/1.00  sup_bw_superposition:                   13
% 2.03/1.00  sup_immediate_simplified:               0
% 2.03/1.00  sup_given_eliminated:                   0
% 2.03/1.00  comparisons_done:                       0
% 2.03/1.00  comparisons_avoided:                    24
% 2.03/1.00  
% 2.03/1.00  ------ Simplifications
% 2.03/1.00  
% 2.03/1.00  
% 2.03/1.00  sim_fw_subset_subsumed:                 0
% 2.03/1.00  sim_bw_subset_subsumed:                 0
% 2.03/1.00  sim_fw_subsumed:                        0
% 2.03/1.00  sim_bw_subsumed:                        0
% 2.03/1.00  sim_fw_subsumption_res:                 1
% 2.03/1.00  sim_bw_subsumption_res:                 0
% 2.03/1.00  sim_tautology_del:                      1
% 2.03/1.00  sim_eq_tautology_del:                   0
% 2.03/1.00  sim_eq_res_simp:                        0
% 2.03/1.00  sim_fw_demodulated:                     0
% 2.03/1.00  sim_bw_demodulated:                     3
% 2.03/1.00  sim_light_normalised:                   1
% 2.03/1.00  sim_joinable_taut:                      0
% 2.03/1.00  sim_joinable_simp:                      0
% 2.03/1.00  sim_ac_normalised:                      0
% 2.03/1.00  sim_smt_subsumption:                    0
% 2.03/1.00  
%------------------------------------------------------------------------------
