%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 269 expanded)
%              Number of leaves         :    3 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  226 (1300 expanded)
%              Number of equality atoms :  196 (1077 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(subsumption_resolution,[],[f115,f9])).

fof(f9,plain,(
    sK4 != k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) != X4
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ~ ! [X4] :
                ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
               => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f115,plain,(
    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(backward_demodulation,[],[f93,f114])).

fof(f114,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f113,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f5])).

fof(f113,plain,
    ( k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f112,f12])).

fof(f12,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f5])).

fof(f112,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f111,f11])).

fof(f11,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f5])).

fof(f111,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f110,f10])).

fof(f10,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f5])).

fof(f110,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f42,f8])).

fof(f8,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X26,X24,X27,X25] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X24,X25,X26,X27))
      | k1_xboole_0 = X24
      | k1_xboole_0 = X25
      | k1_xboole_0 = X26
      | k1_xboole_0 = X27
      | sK5(sK0,sK1,sK2,sK3,sK4) = k8_mcart_1(X24,X25,X26,X27,sK4) ) ),
    inference(superposition,[],[f26,f35])).

fof(f35,plain,(
    sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f34,f13])).

fof(f34,plain,
    ( k1_xboole_0 = sK3
    | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f33,f12])).

fof(f33,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f32,f11])).

fof(f32,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f28,f10])).

fof(f28,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(resolution,[],[f8,f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f26,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X5 ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).

fof(f93,plain,(
    sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(backward_demodulation,[],[f71,f92])).

fof(f92,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f91,f13])).

fof(f91,plain,
    ( k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f90,f12])).

fof(f90,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f89,f11])).

fof(f89,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f88,f10])).

fof(f88,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f40,f8])).

fof(f40,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X16,X17,X18,X19))
      | k1_xboole_0 = X16
      | k1_xboole_0 = X17
      | k1_xboole_0 = X18
      | k1_xboole_0 = X19
      | sK6(sK0,sK1,sK2,sK3,sK4) = k9_mcart_1(X16,X17,X18,X19,sK4) ) ),
    inference(superposition,[],[f25,f35])).

fof(f25,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X6 ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(backward_demodulation,[],[f50,f70])).

fof(f70,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f69,f13])).

fof(f69,plain,
    ( k1_xboole_0 = sK3
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f68,f12])).

fof(f68,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f67,f11])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f66,f10])).

fof(f66,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f38,f8])).

fof(f38,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X8,X9,X10,X11))
      | k1_xboole_0 = X8
      | k1_xboole_0 = X9
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11
      | sK7(sK0,sK1,sK2,sK3,sK4) = k10_mcart_1(X8,X9,X10,X11,sK4) ) ),
    inference(superposition,[],[f24,f35])).

fof(f24,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(backward_demodulation,[],[f35,f48])).

fof(f48,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f47,f13])).

fof(f47,plain,
    ( k1_xboole_0 = sK3
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f46,f12])).

fof(f46,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f45,f11])).

fof(f45,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f44,f10])).

fof(f44,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f36,f8])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | sK8(sK0,sK1,sK2,sK3,sK4) = k11_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f23,f35])).

fof(f23,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (24854)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (24862)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (24864)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (24871)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (24855)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (24863)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (24863)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f115,f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    sK4 != k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (? [X4] : (k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) != X4 & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    inference(negated_conjecture,[],[f3])).
% 0.20/0.48  fof(f3,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(backward_demodulation,[],[f93,f114])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f113,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    k1_xboole_0 != sK3),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f112,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    k1_xboole_0 != sK2),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f111,f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    k1_xboole_0 != sK1),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f110,f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(resolution,[],[f42,f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X26,X24,X27,X25] : (~m1_subset_1(sK4,k4_zfmisc_1(X24,X25,X26,X27)) | k1_xboole_0 = X24 | k1_xboole_0 = X25 | k1_xboole_0 = X26 | k1_xboole_0 = X27 | sK5(sK0,sK1,sK2,sK3,sK4) = k8_mcart_1(X24,X25,X26,X27,sK4)) )),
% 0.20/0.48    inference(superposition,[],[f26,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(subsumption_resolution,[],[f34,f13])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(subsumption_resolution,[],[f33,f12])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(subsumption_resolution,[],[f32,f11])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(subsumption_resolution,[],[f28,f10])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(resolution,[],[f8,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)) = X4) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X5) )),
% 0.20/0.48    inference(equality_resolution,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (! [X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(backward_demodulation,[],[f71,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f91,f13])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f90,f12])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f89,f11])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f88,f10])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(resolution,[],[f40,f8])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X19,X17,X18,X16] : (~m1_subset_1(sK4,k4_zfmisc_1(X16,X17,X18,X19)) | k1_xboole_0 = X16 | k1_xboole_0 = X17 | k1_xboole_0 = X18 | k1_xboole_0 = X19 | sK6(sK0,sK1,sK2,sK3,sK4) = k9_mcart_1(X16,X17,X18,X19,sK4)) )),
% 0.20/0.48    inference(superposition,[],[f25,f35])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X6) )),
% 0.20/0.48    inference(equality_resolution,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(backward_demodulation,[],[f50,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f69,f13])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f68,f12])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f67,f11])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f66,f10])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(resolution,[],[f38,f8])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK4,k4_zfmisc_1(X8,X9,X10,X11)) | k1_xboole_0 = X8 | k1_xboole_0 = X9 | k1_xboole_0 = X10 | k1_xboole_0 = X11 | sK7(sK0,sK1,sK2,sK3,sK4) = k10_mcart_1(X8,X9,X10,X11,sK4)) )),
% 0.20/0.48    inference(superposition,[],[f24,f35])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7) )),
% 0.20/0.48    inference(equality_resolution,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))),
% 0.20/0.48    inference(backward_demodulation,[],[f35,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f47,f13])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f46,f12])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f45,f11])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f44,f10])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.48    inference(resolution,[],[f36,f8])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | sK8(sK0,sK1,sK2,sK3,sK4) = k11_mcart_1(X0,X1,X2,X3,sK4)) )),
% 0.20/0.48    inference(superposition,[],[f23,f35])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8) )),
% 0.20/0.48    inference(equality_resolution,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (24863)------------------------------
% 0.20/0.48  % (24863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24863)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (24863)Memory used [KB]: 1663
% 0.20/0.48  % (24863)Time elapsed: 0.070 s
% 0.20/0.48  % (24863)------------------------------
% 0.20/0.48  % (24863)------------------------------
% 0.20/0.48  % (24845)Success in time 0.125 s
%------------------------------------------------------------------------------
