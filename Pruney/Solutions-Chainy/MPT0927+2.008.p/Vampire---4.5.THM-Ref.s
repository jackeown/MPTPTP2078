%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 434 expanded)
%              Number of leaves         :   13 ( 168 expanded)
%              Depth                    :   26
%              Number of atoms          :  377 (2803 expanded)
%              Number of equality atoms :  149 ( 272 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(subsumption_resolution,[],[f141,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f141,plain,(
    ~ r1_tarski(k1_xboole_0,k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))) ),
    inference(backward_demodulation,[],[f75,f135])).

fof(f135,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f127,f29])).

fof(f127,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f78,f121])).

fof(f121,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f113,f29])).

fof(f113,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f72,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f99,f29])).

fof(f99,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_mcart_1(sK8))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f69,f93])).

fof(f93,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f92,f51])).

fof(f51,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f49,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f48,f33])).

fof(f48,plain,(
    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f35,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f27,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f11,f20,f19,f18,f17,f16])).

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

fof(f17,plain,
    ( ? [X5] :
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
   => ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                  & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                  & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
              & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ? [X8] :
                ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                  | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                  | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                  | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
            & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
        & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
   => ( ? [X7] :
          ( ? [X8] :
              ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
                | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
              & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
              & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
          & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X7] :
        ( ? [X8] :
            ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
              | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
              | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
              | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
            & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
            & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
        & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
   => ( ? [X8] :
          ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
            | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
            | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
            | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
          & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
          & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & m1_subset_1(sK7,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X8] :
        ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
          | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
          | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
          | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
        & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
        & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
   => ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
      & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
      & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).

fof(f92,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f89,f90])).

fof(f90,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f46,f42])).

fof(f42,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f26,f40])).

fof(f26,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f89,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f88,f56])).

fof(f56,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    inference(resolution,[],[f34,f49])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f85,f86])).

fof(f86,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f45,f42])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,
    ( ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f84,f55])).

fof(f55,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    inference(resolution,[],[f34,f48])).

fof(f84,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f81,f82])).

fof(f82,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f44,f42])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,
    ( ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f80,f54])).

fof(f54,plain,(
    r2_hidden(k2_mcart_1(sK8),sK7) ),
    inference(resolution,[],[f34,f41])).

fof(f80,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f28,f79])).

fof(f79,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f43,f42])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ~ r1_tarski(sK3,k2_mcart_1(sK8)) ),
    inference(resolution,[],[f67,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f67,plain,(
    r2_hidden(k2_mcart_1(sK8),sK3) ),
    inference(resolution,[],[f66,f25])).

fof(f25,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X6] :
      ( ~ m1_subset_1(sK7,k1_zfmisc_1(X6))
      | r2_hidden(k2_mcart_1(sK8),X6) ) ),
    inference(resolution,[],[f30,f54])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f72,plain,(
    ~ r1_tarski(sK2,k2_mcart_1(k1_mcart_1(sK8))) ),
    inference(resolution,[],[f70,f31])).

fof(f70,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK2) ),
    inference(resolution,[],[f65,f24])).

fof(f24,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X5))
      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),X5) ) ),
    inference(resolution,[],[f30,f55])).

fof(f78,plain,(
    ~ r1_tarski(sK1,k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))) ),
    inference(resolution,[],[f76,f31])).

fof(f76,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK1) ),
    inference(resolution,[],[f64,f23])).

fof(f23,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X4))
      | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),X4) ) ),
    inference(resolution,[],[f30,f56])).

fof(f75,plain,(
    ~ r1_tarski(sK0,k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))) ),
    inference(resolution,[],[f73,f31])).

fof(f73,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK0) ),
    inference(resolution,[],[f63,f22])).

fof(f22,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X3))
      | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),X3) ) ),
    inference(resolution,[],[f30,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (21171)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (21171)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (21163)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (21162)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (21164)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f141,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))))),
% 0.20/0.47    inference(backward_demodulation,[],[f75,f135])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    k1_xboole_0 = sK0),
% 0.20/0.47    inference(subsumption_resolution,[],[f127,f29])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))) | k1_xboole_0 = sK0),
% 0.20/0.47    inference(superposition,[],[f78,f121])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(subsumption_resolution,[],[f113,f29])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,k2_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(superposition,[],[f72,f107])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(subsumption_resolution,[],[f99,f29])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,k2_mcart_1(sK8)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(superposition,[],[f69,f93])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(subsumption_resolution,[],[f92,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)),
% 0.20/0.47    inference(resolution,[],[f49,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))),
% 0.20/0.47    inference(resolution,[],[f48,f33])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 0.20/0.47    inference(resolution,[],[f33,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.20/0.47    inference(definition_unfolding,[],[f27,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f35,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    (((((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f11,f20,f19,f18,f17,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) => ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f91])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(superposition,[],[f89,f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(resolution,[],[f46,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.20/0.47    inference(definition_unfolding,[],[f26,f40])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f36,f40])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(subsumption_resolution,[],[f88,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)),
% 0.20/0.47    inference(resolution,[],[f34,f49])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(superposition,[],[f85,f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(resolution,[],[f45,f42])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f37,f40])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(subsumption_resolution,[],[f84,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)),
% 0.20/0.47    inference(resolution,[],[f34,f48])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(superposition,[],[f81,f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(resolution,[],[f44,f42])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f38,f40])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(subsumption_resolution,[],[f80,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(sK8),sK7)),
% 0.20/0.47    inference(resolution,[],[f34,f41])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ~r2_hidden(k2_mcart_1(sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(superposition,[],[f28,f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.47    inference(resolution,[],[f43,f42])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f39,f40])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ~r1_tarski(sK3,k2_mcart_1(sK8))),
% 0.20/0.47    inference(resolution,[],[f67,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(sK8),sK3)),
% 0.20/0.47    inference(resolution,[],[f66,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X6] : (~m1_subset_1(sK7,k1_zfmisc_1(X6)) | r2_hidden(k2_mcart_1(sK8),X6)) )),
% 0.20/0.47    inference(resolution,[],[f30,f54])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k2_mcart_1(k1_mcart_1(sK8)))),
% 0.20/0.47    inference(resolution,[],[f70,f31])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK2)),
% 0.20/0.47    inference(resolution,[],[f65,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X5] : (~m1_subset_1(sK6,k1_zfmisc_1(X5)) | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),X5)) )),
% 0.20/0.47    inference(resolution,[],[f30,f55])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ~r1_tarski(sK1,k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))))),
% 0.20/0.47    inference(resolution,[],[f76,f31])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK1)),
% 0.20/0.47    inference(resolution,[],[f64,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X4] : (~m1_subset_1(sK5,k1_zfmisc_1(X4)) | r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),X4)) )),
% 0.20/0.47    inference(resolution,[],[f30,f56])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ~r1_tarski(sK0,k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))))),
% 0.20/0.47    inference(resolution,[],[f73,f31])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK0)),
% 0.20/0.47    inference(resolution,[],[f63,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X3] : (~m1_subset_1(sK4,k1_zfmisc_1(X3)) | r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),X3)) )),
% 0.20/0.47    inference(resolution,[],[f30,f51])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (21171)------------------------------
% 0.20/0.47  % (21171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (21171)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (21171)Memory used [KB]: 1791
% 0.20/0.47  % (21171)Time elapsed: 0.063 s
% 0.20/0.47  % (21171)------------------------------
% 0.20/0.47  % (21171)------------------------------
% 0.20/0.48  % (21159)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (21173)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (21157)Success in time 0.122 s
%------------------------------------------------------------------------------
