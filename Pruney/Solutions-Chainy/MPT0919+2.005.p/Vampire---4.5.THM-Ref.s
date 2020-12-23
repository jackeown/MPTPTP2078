%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:43 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 336 expanded)
%              Number of leaves         :    5 (  72 expanded)
%              Depth                    :   23
%              Number of atoms          :  320 (2276 expanded)
%              Number of equality atoms :  223 (1395 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(subsumption_resolution,[],[f92,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X6 ) ) ) ) )
         => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X6 ) ) ) ) )
       => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).

fof(f92,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f91,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f91,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f90,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f90,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f89,f14])).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f88,f18])).

fof(f18,plain,(
    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,
    ( sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f80,f31])).

fof(f31,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f13,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f13,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | sK4 = k8_mcart_1(X0,X1,X2,X3,sK5)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(backward_demodulation,[],[f70,f79])).

fof(f79,plain,(
    sK4 = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f78,f49])).

fof(f49,plain,(
    m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f48,f14])).

fof(f48,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f47,f17])).

fof(f47,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f46,f16])).

fof(f46,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f45,f15])).

fof(f45,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(resolution,[],[f32,f31])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f9])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f78,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f77,f64])).

fof(f64,plain,(
    m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f63,f14])).

fof(f63,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f62,f17])).

fof(f62,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f61,f16])).

fof(f61,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(subsumption_resolution,[],[f60,f15])).

fof(f60,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(resolution,[],[f36,f31])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ),
    inference(definition_unfolding,[],[f21,f30])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f77,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f76,f59])).

fof(f59,plain,(
    m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f58,f14])).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f57,f17])).

fof(f57,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f56,f16])).

fof(f56,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(subsumption_resolution,[],[f55,f15])).

fof(f55,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(resolution,[],[f34,f31])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f76,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f75,f54])).

fof(f54,plain,(
    m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f53,f14])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f52,f17])).

fof(f52,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f51,f16])).

fof(f51,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(subsumption_resolution,[],[f50,f15])).

fof(f50,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(resolution,[],[f33,f31])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( sK5 != sK5
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK6(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[],[f12,f69])).

fof(f69,plain,(
    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f68,f14])).

fof(f68,plain,
    ( k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f67,f17])).

fof(f67,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f66,f16])).

fof(f66,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f65,f15])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(resolution,[],[f35,f31])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(definition_unfolding,[],[f22,f30])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X6 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | sK6(sK0,sK1,sK2,sK3,sK5) = k8_mcart_1(X0,X1,X2,X3,sK5) ) ),
    inference(superposition,[],[f44,f69])).

fof(f44,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X5 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:17:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (15616)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (15638)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (15622)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (15630)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (15613)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (15612)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (15624)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.26/0.53  % (15616)Refutation found. Thanks to Tanya!
% 1.26/0.53  % SZS status Theorem for theBenchmark
% 1.26/0.53  % SZS output start Proof for theBenchmark
% 1.26/0.53  fof(f93,plain,(
% 1.26/0.53    $false),
% 1.26/0.53    inference(subsumption_resolution,[],[f92,f17])).
% 1.26/0.53  fof(f17,plain,(
% 1.26/0.53    k1_xboole_0 != sK3),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f8,plain,(
% 1.26/0.53    ? [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.26/0.53    inference(flattening,[],[f7])).
% 1.26/0.53  fof(f7,plain,(
% 1.26/0.53    ? [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.26/0.53    inference(ennf_transformation,[],[f6])).
% 1.26/0.53  fof(f6,negated_conjecture,(
% 1.26/0.53    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.26/0.53    inference(negated_conjecture,[],[f5])).
% 1.26/0.53  fof(f5,conjecture,(
% 1.26/0.53    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).
% 1.26/0.53  fof(f92,plain,(
% 1.26/0.53    k1_xboole_0 = sK3),
% 1.26/0.53    inference(subsumption_resolution,[],[f91,f16])).
% 1.26/0.53  fof(f16,plain,(
% 1.26/0.53    k1_xboole_0 != sK2),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f91,plain,(
% 1.26/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3),
% 1.26/0.53    inference(subsumption_resolution,[],[f90,f15])).
% 1.26/0.53  fof(f15,plain,(
% 1.26/0.53    k1_xboole_0 != sK1),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f90,plain,(
% 1.26/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3),
% 1.26/0.53    inference(subsumption_resolution,[],[f89,f14])).
% 1.26/0.53  fof(f14,plain,(
% 1.26/0.53    k1_xboole_0 != sK0),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f89,plain,(
% 1.26/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3),
% 1.26/0.53    inference(subsumption_resolution,[],[f88,f18])).
% 1.26/0.53  fof(f18,plain,(
% 1.26/0.53    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f88,plain,(
% 1.26/0.53    sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3),
% 1.26/0.53    inference(resolution,[],[f80,f31])).
% 1.26/0.53  fof(f31,plain,(
% 1.26/0.53    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 1.26/0.53    inference(definition_unfolding,[],[f13,f30])).
% 1.26/0.53  fof(f30,plain,(
% 1.26/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.26/0.53    inference(definition_unfolding,[],[f20,f19])).
% 1.26/0.53  fof(f19,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f1])).
% 1.26/0.53  fof(f1,axiom,(
% 1.26/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.26/0.53  fof(f20,plain,(
% 1.26/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f2])).
% 1.26/0.53  fof(f2,axiom,(
% 1.26/0.53    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.26/0.53  fof(f13,plain,(
% 1.26/0.53    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f80,plain,(
% 1.26/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | sK4 = k8_mcart_1(X0,X1,X2,X3,sK5) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 1.26/0.53    inference(backward_demodulation,[],[f70,f79])).
% 1.26/0.53  fof(f79,plain,(
% 1.26/0.53    sK4 = sK6(sK0,sK1,sK2,sK3,sK5)),
% 1.26/0.53    inference(subsumption_resolution,[],[f78,f49])).
% 1.26/0.53  fof(f49,plain,(
% 1.26/0.53    m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 1.26/0.53    inference(subsumption_resolution,[],[f48,f14])).
% 1.26/0.53  fof(f48,plain,(
% 1.26/0.53    k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 1.26/0.53    inference(subsumption_resolution,[],[f47,f17])).
% 1.26/0.53  fof(f47,plain,(
% 1.26/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 1.26/0.53    inference(subsumption_resolution,[],[f46,f16])).
% 1.26/0.53  fof(f46,plain,(
% 1.26/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 1.26/0.53    inference(subsumption_resolution,[],[f45,f15])).
% 1.26/0.53  fof(f45,plain,(
% 1.26/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 1.26/0.53    inference(resolution,[],[f32,f31])).
% 1.26/0.53  fof(f32,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) )),
% 1.26/0.53    inference(definition_unfolding,[],[f25,f30])).
% 1.26/0.53  fof(f25,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f9])).
% 1.26/0.53  fof(f9,plain,(
% 1.26/0.53    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.26/0.53    inference(ennf_transformation,[],[f3])).
% 1.26/0.53  fof(f3,axiom,(
% 1.26/0.53    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).
% 1.26/0.53  fof(f78,plain,(
% 1.26/0.53    ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK6(sK0,sK1,sK2,sK3,sK5)),
% 1.26/0.53    inference(subsumption_resolution,[],[f77,f64])).
% 1.26/0.53  fof(f64,plain,(
% 1.26/0.53    m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 1.26/0.53    inference(subsumption_resolution,[],[f63,f14])).
% 1.26/0.53  fof(f63,plain,(
% 1.26/0.53    k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 1.26/0.53    inference(subsumption_resolution,[],[f62,f17])).
% 1.26/0.53  fof(f62,plain,(
% 1.26/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 1.26/0.53    inference(subsumption_resolution,[],[f61,f16])).
% 1.26/0.53  fof(f61,plain,(
% 1.26/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 1.26/0.53    inference(subsumption_resolution,[],[f60,f15])).
% 1.26/0.53  fof(f60,plain,(
% 1.26/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 1.26/0.53    inference(resolution,[],[f36,f31])).
% 1.26/0.53  fof(f36,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) )),
% 1.26/0.53    inference(definition_unfolding,[],[f21,f30])).
% 1.26/0.53  fof(f21,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f9])).
% 1.26/0.53  fof(f77,plain,(
% 1.26/0.53    ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK6(sK0,sK1,sK2,sK3,sK5)),
% 1.26/0.53    inference(subsumption_resolution,[],[f76,f59])).
% 1.26/0.53  fof(f59,plain,(
% 1.26/0.53    m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f58,f14])).
% 1.26/0.53  fof(f58,plain,(
% 1.26/0.53    k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f57,f17])).
% 1.26/0.53  fof(f57,plain,(
% 1.26/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f56,f16])).
% 1.26/0.53  fof(f56,plain,(
% 1.26/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 1.26/0.53    inference(subsumption_resolution,[],[f55,f15])).
% 1.26/0.53  fof(f55,plain,(
% 1.26/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 1.26/0.53    inference(resolution,[],[f34,f31])).
% 1.26/0.53  fof(f34,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) )),
% 1.26/0.53    inference(definition_unfolding,[],[f23,f30])).
% 1.26/0.53  fof(f23,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f9])).
% 1.26/0.53  fof(f76,plain,(
% 1.26/0.53    ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK6(sK0,sK1,sK2,sK3,sK5)),
% 1.26/0.53    inference(subsumption_resolution,[],[f75,f54])).
% 1.26/0.53  fof(f54,plain,(
% 1.26/0.53    m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 1.26/0.53    inference(subsumption_resolution,[],[f53,f14])).
% 1.26/0.53  fof(f53,plain,(
% 1.26/0.53    k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 1.26/0.53    inference(subsumption_resolution,[],[f52,f17])).
% 1.26/0.53  fof(f52,plain,(
% 1.26/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 1.26/0.53    inference(subsumption_resolution,[],[f51,f16])).
% 1.26/0.53  fof(f51,plain,(
% 1.26/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 1.26/0.53    inference(subsumption_resolution,[],[f50,f15])).
% 1.26/0.53  fof(f50,plain,(
% 1.26/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 1.26/0.53    inference(resolution,[],[f33,f31])).
% 1.26/0.53  fof(f33,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) )),
% 1.26/0.53    inference(definition_unfolding,[],[f24,f30])).
% 1.26/0.53  fof(f24,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f9])).
% 1.26/0.53  fof(f75,plain,(
% 1.26/0.53    ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK6(sK0,sK1,sK2,sK3,sK5)),
% 1.26/0.53    inference(trivial_inequality_removal,[],[f74])).
% 1.26/0.53  fof(f74,plain,(
% 1.26/0.53    sK5 != sK5 | ~m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK6(sK0,sK1,sK2,sK3,sK5)),
% 1.26/0.53    inference(superposition,[],[f12,f69])).
% 1.26/0.53  fof(f69,plain,(
% 1.26/0.53    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))),
% 1.26/0.53    inference(subsumption_resolution,[],[f68,f14])).
% 1.26/0.53  fof(f68,plain,(
% 1.26/0.53    k1_xboole_0 = sK0 | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))),
% 1.26/0.53    inference(subsumption_resolution,[],[f67,f17])).
% 1.26/0.53  fof(f67,plain,(
% 1.26/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))),
% 1.26/0.53    inference(subsumption_resolution,[],[f66,f16])).
% 1.26/0.53  fof(f66,plain,(
% 1.26/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))),
% 1.26/0.53    inference(subsumption_resolution,[],[f65,f15])).
% 1.26/0.53  fof(f65,plain,(
% 1.26/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))),
% 1.26/0.53    inference(resolution,[],[f35,f31])).
% 1.26/0.53  fof(f35,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 1.26/0.53    inference(definition_unfolding,[],[f22,f30])).
% 1.26/0.53  fof(f22,plain,(
% 1.26/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 1.26/0.53    inference(cnf_transformation,[],[f9])).
% 1.26/0.53  fof(f12,plain,(
% 1.26/0.53    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X6) )),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f70,plain,(
% 1.26/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | sK6(sK0,sK1,sK2,sK3,sK5) = k8_mcart_1(X0,X1,X2,X3,sK5)) )),
% 1.26/0.53    inference(superposition,[],[f44,f69])).
% 1.26/0.53  fof(f44,plain,(
% 1.26/0.53    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X5) )),
% 1.26/0.53    inference(equality_resolution,[],[f40])).
% 1.26/0.53  fof(f40,plain,(
% 1.26/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 1.26/0.53    inference(definition_unfolding,[],[f26,f30])).
% 1.26/0.53  fof(f26,plain,(
% 1.26/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 1.26/0.53    inference(cnf_transformation,[],[f11])).
% 1.26/0.53  fof(f11,plain,(
% 1.26/0.53    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.26/0.53    inference(flattening,[],[f10])).
% 1.26/0.53  fof(f10,plain,(
% 1.26/0.53    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.26/0.53    inference(ennf_transformation,[],[f4])).
% 1.26/0.53  fof(f4,axiom,(
% 1.26/0.53    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 1.26/0.53  % SZS output end Proof for theBenchmark
% 1.26/0.53  % (15616)------------------------------
% 1.26/0.53  % (15616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (15616)Termination reason: Refutation
% 1.26/0.53  
% 1.26/0.53  % (15616)Memory used [KB]: 6268
% 1.26/0.53  % (15616)Time elapsed: 0.117 s
% 1.26/0.53  % (15616)------------------------------
% 1.26/0.53  % (15616)------------------------------
% 1.26/0.53  % (15615)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.53  % (15609)Success in time 0.167 s
%------------------------------------------------------------------------------
