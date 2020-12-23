%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0918+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 192 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :   18
%              Number of atoms          :  370 (1348 expanded)
%              Number of equality atoms :  288 (1167 expanded)
%              Maximal formula depth    :   20 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(subsumption_resolution,[],[f154,f147])).

fof(f147,plain,(
    sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f141])).

fof(f141,plain,
    ( sK7 != sK7
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f134,f140])).

fof(f140,plain,(
    sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f139,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f139,plain,
    ( k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f138,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f138,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f137,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f137,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f136,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f136,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f58,f23])).

fof(f23,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X8,X9,X10,X11))
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11
      | k1_xboole_0 = X9
      | k1_xboole_0 = X8
      | sK7 = k10_mcart_1(X8,X9,X10,X11,sK4) ) ),
    inference(subsumption_resolution,[],[f54,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f54,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(k10_mcart_1(X8,X9,X10,X11,sK4),X10)
      | k1_xboole_0 = X9
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11
      | ~ m1_subset_1(sK4,k4_zfmisc_1(X8,X9,X10,X11))
      | k1_xboole_0 = X8
      | sK7 = k10_mcart_1(X8,X9,X10,X11,sK4) ) ),
    inference(superposition,[],[f47,f22])).

fof(f22,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) = X8 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X2)
      | X5 = X8
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) != X5 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f134,plain,
    ( sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( sK6 != sK6
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(superposition,[],[f121,f128])).

fof(f128,plain,(
    sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f127,f24])).

fof(f127,plain,
    ( k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f126,f25])).

fof(f126,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f125,f27])).

fof(f125,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f124,f26])).

fof(f124,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f57,f23])).

fof(f57,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X4,X5,X6,X7))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | sK6 = k9_mcart_1(X4,X5,X6,X7,sK4) ) ),
    inference(subsumption_resolution,[],[f53,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f53,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(k9_mcart_1(X4,X5,X6,X7,sK4),X5)
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | ~ m1_subset_1(sK4,k4_zfmisc_1(X4,X5,X6,X7))
      | k1_xboole_0 = X4
      | sK6 = k9_mcart_1(X4,X5,X6,X7,sK4) ) ),
    inference(superposition,[],[f49,f22])).

fof(f49,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) = X7 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X1)
      | X5 = X7
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) != X5 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f121,plain,
    ( sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,
    ( sK5 != sK5
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f21,f116])).

fof(f116,plain,(
    sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f115,f24])).

fof(f115,plain,
    ( k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f114,f25])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f113,f27])).

fof(f113,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f112,f26])).

fof(f112,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f56,f23])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,sK4),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f51,f22])).

fof(f51,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) = X6 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X0)
      | X5 = X6
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) != X5 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f21,plain,
    ( sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f154,plain,(
    sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f153,f24])).

fof(f153,plain,
    ( k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f152,f25])).

fof(f152,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f151,f27])).

fof(f151,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f150,f26])).

fof(f150,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f59,f23])).

fof(f59,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X12,X13,X14,X15))
      | k1_xboole_0 = X14
      | k1_xboole_0 = X15
      | k1_xboole_0 = X13
      | k1_xboole_0 = X12
      | sK8 = k11_mcart_1(X12,X13,X14,X15,sK4) ) ),
    inference(subsumption_resolution,[],[f55,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f55,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(k11_mcart_1(X12,X13,X14,X15,sK4),X15)
      | k1_xboole_0 = X13
      | k1_xboole_0 = X14
      | k1_xboole_0 = X15
      | ~ m1_subset_1(sK4,k4_zfmisc_1(X12,X13,X14,X15))
      | k1_xboole_0 = X12
      | sK8 = k11_mcart_1(X12,X13,X14,X15,sK4) ) ),
    inference(superposition,[],[f45,f22])).

fof(f45,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) = X9 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X3)
      | X5 = X9
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) != X5 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

%------------------------------------------------------------------------------
