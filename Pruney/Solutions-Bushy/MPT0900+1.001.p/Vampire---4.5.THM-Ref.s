%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0900+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:51 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 289 expanded)
%              Number of leaves         :   10 (  59 expanded)
%              Depth                    :   20
%              Number of atoms          :  374 (1388 expanded)
%              Number of equality atoms :  282 (1109 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(subsumption_resolution,[],[f197,f23])).

fof(f23,plain,(
    sK4 != k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) != X4
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ~ ! [X4] :
                ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
               => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f197,plain,(
    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(backward_demodulation,[],[f184,f193])).

fof(f193,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f192,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f192,plain,
    ( k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f191,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f191,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f190,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f190,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f189,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f189,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f149,f22])).

fof(f22,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f149,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X12,X13,X14,X15))
      | k1_xboole_0 = X14
      | k1_xboole_0 = X15
      | k1_xboole_0 = X13
      | k1_xboole_0 = X12
      | sK6(sK0,sK1,sK2,sK3,sK4) = k9_mcart_1(X12,X13,X14,X15,sK4) ) ),
    inference(subsumption_resolution,[],[f145,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f145,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(k9_mcart_1(X12,X13,X14,X15,sK4),X13)
      | k1_xboole_0 = X13
      | k1_xboole_0 = X14
      | k1_xboole_0 = X15
      | ~ m1_subset_1(sK4,k4_zfmisc_1(X12,X13,X14,X15))
      | k1_xboole_0 = X12
      | sK6(sK0,sK1,sK2,sK3,sK4) = k9_mcart_1(X12,X13,X14,X15,sK4) ) ),
    inference(superposition,[],[f50,f81])).

fof(f81,plain,(
    sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f80,f24])).

fof(f80,plain,
    ( k1_xboole_0 = sK0
    | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f79,f27])).

fof(f79,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f78,f26])).

fof(f78,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f58,f25])).

fof(f58,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(resolution,[],[f22,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f50,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) = X7 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X1)
      | X5 = X7
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) != X5 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X1)
      | k4_mcart_1(X6,X7,X8,X9) != X4
      | X5 = X7
      | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X7 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_mcart_1)).

fof(f184,plain,(
    sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(backward_demodulation,[],[f171,f180])).

fof(f180,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f179,f24])).

fof(f179,plain,
    ( k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f178,f25])).

fof(f178,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f177,f27])).

fof(f177,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f176,f26])).

fof(f176,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f148,f22])).

fof(f148,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X8,X9,X10,X11))
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11
      | k1_xboole_0 = X9
      | k1_xboole_0 = X8
      | sK5(sK0,sK1,sK2,sK3,sK4) = k8_mcart_1(X8,X9,X10,X11,sK4) ) ),
    inference(subsumption_resolution,[],[f144,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f144,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(k8_mcart_1(X8,X9,X10,X11,sK4),X8)
      | k1_xboole_0 = X9
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11
      | ~ m1_subset_1(sK4,k4_zfmisc_1(X8,X9,X10,X11))
      | k1_xboole_0 = X8
      | sK5(sK0,sK1,sK2,sK3,sK4) = k8_mcart_1(X8,X9,X10,X11,sK4) ) ),
    inference(superposition,[],[f52,f81])).

fof(f52,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) = X6 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X0)
      | X5 = X6
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) != X5 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X0)
      | k4_mcart_1(X6,X7,X8,X9) != X4
      | X5 = X6
      | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X6
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X6 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_mcart_1)).

fof(f171,plain,(
    sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(backward_demodulation,[],[f155,f167])).

fof(f167,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f166,f24])).

fof(f166,plain,
    ( k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f165,f25])).

fof(f165,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f164,f27])).

fof(f164,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f163,f26])).

fof(f163,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f147,f22])).

fof(f147,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X4,X5,X6,X7))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | sK8(sK0,sK1,sK2,sK3,sK4) = k11_mcart_1(X4,X5,X6,X7,sK4) ) ),
    inference(subsumption_resolution,[],[f143,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f143,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k11_mcart_1(X4,X5,X6,X7,sK4),X7)
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | ~ m1_subset_1(sK4,k4_zfmisc_1(X4,X5,X6,X7))
      | k1_xboole_0 = X4
      | sK8(sK0,sK1,sK2,sK3,sK4) = k11_mcart_1(X4,X5,X6,X7,sK4) ) ),
    inference(superposition,[],[f54,f81])).

fof(f54,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) = X9 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X3)
      | X5 = X9
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) != X5 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X3)
      | k4_mcart_1(X6,X7,X8,X9) != X4
      | X5 = X9
      | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X9
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X3)
                 => ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X9 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_mcart_1)).

fof(f155,plain,(
    sK4 = k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) ),
    inference(backward_demodulation,[],[f81,f154])).

fof(f154,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f153,f24])).

fof(f153,plain,
    ( k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f152,f25])).

fof(f152,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f151,f27])).

fof(f151,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f150,f26])).

fof(f150,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f146,f22])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK7(sK0,sK1,sK2,sK3,sK4) = k10_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f142,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,sK4),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | sK7(sK0,sK1,sK2,sK3,sK4) = k10_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f56,f81])).

fof(f56,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) = X8 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X2)
      | X5 = X8
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) != X5 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X2)
      | k4_mcart_1(X6,X7,X8,X9) != X4
      | X5 = X8
      | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X2)
                 => ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X8 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_mcart_1)).

%------------------------------------------------------------------------------
