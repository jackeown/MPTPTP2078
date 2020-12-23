%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 403 expanded)
%              Number of leaves         :    5 (  85 expanded)
%              Depth                    :   18
%              Number of atoms          :  332 (2380 expanded)
%              Number of equality atoms :  301 (2143 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(subsumption_resolution,[],[f96,f90])).

fof(f90,plain,(
    sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( sK7 != sK7
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f82,f88])).

fof(f88,plain,(
    sK7 = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(backward_demodulation,[],[f61,f87])).

fof(f87,plain,(
    sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f86,f14])).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f86,plain,
    ( k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f85,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f85,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f84,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f84,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f83,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f83,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f44,f29])).

fof(f29,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f13,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f13,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10),X11))
      | k1_xboole_0 = X9
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11
      | k1_xboole_0 = X8
      | sK7 = k10_mcart_1(X8,X9,X10,X11,sK4) ) ),
    inference(superposition,[],[f39,f12])).

fof(f12,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).

fof(f61,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f60,f14])).

fof(f60,plain,
    ( k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f59,f17])).

fof(f59,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f58,f16])).

fof(f58,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f48,f15])).

fof(f48,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(resolution,[],[f29,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(definition_unfolding,[],[f22,f28])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f82,plain,
    ( sK7 != k2_mcart_1(k1_mcart_1(sK4))
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,
    ( sK6 != sK6
    | sK7 != k2_mcart_1(k1_mcart_1(sK4))
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f74,f80])).

fof(f80,plain,(
    sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(backward_demodulation,[],[f57,f79])).

fof(f79,plain,(
    sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f78,f14])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f77,f17])).

fof(f77,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f76,f16])).

fof(f76,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f75,f15])).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f43,f29])).

fof(f43,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7))
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | k1_xboole_0 = X4
      | sK6 = k9_mcart_1(X4,X5,X6,X7,sK4) ) ),
    inference(superposition,[],[f40,f12])).

fof(f40,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X6 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f56,f14])).

fof(f56,plain,
    ( k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f55,f17])).

fof(f55,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f54,f16])).

fof(f54,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f47,f15])).

fof(f47,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(resolution,[],[f29,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,
    ( sK7 != k2_mcart_1(k1_mcart_1(sK4))
    | sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(forward_demodulation,[],[f73,f61])).

fof(f73,plain,
    ( sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(forward_demodulation,[],[f72,f57])).

fof(f72,plain,
    ( sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f11,f70])).

fof(f70,plain,(
    sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f69,f14])).

fof(f69,plain,
    ( k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f68,f17])).

fof(f68,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f67,f16])).

fof(f67,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f66,f15])).

fof(f66,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f42,f29])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f41,f12])).

fof(f41,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X5 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,plain,
    ( sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f96,plain,(
    sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f95,f14])).

fof(f95,plain,
    ( k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f94,f17])).

fof(f94,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f93,f16])).

fof(f93,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f92,f15])).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f45,f29])).

fof(f45,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14),X15))
      | k1_xboole_0 = X13
      | k1_xboole_0 = X14
      | k1_xboole_0 = X15
      | k1_xboole_0 = X12
      | sK8 = k11_mcart_1(X12,X13,X14,X15,sK4) ) ),
    inference(superposition,[],[f38,f12])).

fof(f38,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(cnf_transformation,[],[f10])).

% (19066)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:37:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (19074)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (19054)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (19073)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (19059)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (19081)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (19073)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f97,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(subsumption_resolution,[],[f96,f90])).
% 1.25/0.53  fof(f90,plain,(
% 1.25/0.53    sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(trivial_inequality_removal,[],[f89])).
% 1.25/0.53  fof(f89,plain,(
% 1.25/0.53    sK7 != sK7 | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(backward_demodulation,[],[f82,f88])).
% 1.25/0.53  fof(f88,plain,(
% 1.25/0.53    sK7 = k2_mcart_1(k1_mcart_1(sK4))),
% 1.25/0.53    inference(backward_demodulation,[],[f61,f87])).
% 1.25/0.53  fof(f87,plain,(
% 1.25/0.53    sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f86,f14])).
% 1.25/0.53  fof(f14,plain,(
% 1.25/0.53    k1_xboole_0 != sK0),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f8,plain,(
% 1.25/0.53    ? [X0,X1,X2,X3,X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.25/0.53    inference(flattening,[],[f7])).
% 1.25/0.53  fof(f7,plain,(
% 1.25/0.53    ? [X0,X1,X2,X3,X4] : ((? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.25/0.53    inference(ennf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,negated_conjecture,(
% 1.25/0.53    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 1.25/0.53    inference(negated_conjecture,[],[f5])).
% 1.25/0.53  fof(f5,conjecture,(
% 1.25/0.53    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).
% 1.25/0.53  fof(f86,plain,(
% 1.25/0.53    k1_xboole_0 = sK0 | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f85,f17])).
% 1.25/0.53  fof(f17,plain,(
% 1.25/0.53    k1_xboole_0 != sK3),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f85,plain,(
% 1.25/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f84,f16])).
% 1.25/0.53  fof(f16,plain,(
% 1.25/0.53    k1_xboole_0 != sK2),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f84,plain,(
% 1.25/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f83,f15])).
% 1.25/0.53  fof(f15,plain,(
% 1.25/0.53    k1_xboole_0 != sK1),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f83,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(resolution,[],[f44,f29])).
% 1.25/0.53  fof(f29,plain,(
% 1.25/0.53    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 1.25/0.53    inference(definition_unfolding,[],[f13,f28])).
% 1.25/0.53  fof(f28,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f19,f18])).
% 1.25/0.53  fof(f18,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f1])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.25/0.53  fof(f19,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.25/0.53  fof(f13,plain,(
% 1.25/0.53    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f44,plain,(
% 1.25/0.53    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10),X11)) | k1_xboole_0 = X9 | k1_xboole_0 = X10 | k1_xboole_0 = X11 | k1_xboole_0 = X8 | sK7 = k10_mcart_1(X8,X9,X10,X11,sK4)) )),
% 1.25/0.53    inference(superposition,[],[f39,f12])).
% 1.25/0.53  fof(f12,plain,(
% 1.25/0.53    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f39,plain,(
% 1.25/0.53    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7) )),
% 1.25/0.53    inference(equality_resolution,[],[f35])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 1.25/0.53    inference(definition_unfolding,[],[f26,f28])).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 1.25/0.53    inference(cnf_transformation,[],[f10])).
% 1.25/0.53  fof(f10,plain,(
% 1.25/0.53    ! [X0,X1,X2,X3] : (! [X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.25/0.53    inference(ennf_transformation,[],[f3])).
% 1.25/0.53  fof(f3,axiom,(
% 1.25/0.53    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).
% 1.25/0.53  fof(f61,plain,(
% 1.25/0.53    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 1.25/0.53    inference(subsumption_resolution,[],[f60,f14])).
% 1.25/0.53  fof(f60,plain,(
% 1.25/0.53    k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 1.25/0.53    inference(subsumption_resolution,[],[f59,f17])).
% 1.25/0.53  fof(f59,plain,(
% 1.25/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 1.25/0.53    inference(subsumption_resolution,[],[f58,f16])).
% 1.25/0.53  fof(f58,plain,(
% 1.25/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 1.25/0.53    inference(subsumption_resolution,[],[f48,f15])).
% 1.25/0.53  fof(f48,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 1.25/0.53    inference(resolution,[],[f29,f31])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f22,f28])).
% 1.25/0.53  fof(f22,plain,(
% 1.25/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f9])).
% 1.25/0.53  fof(f9,plain,(
% 1.25/0.53    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.25/0.53    inference(ennf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).
% 1.25/0.53  fof(f82,plain,(
% 1.25/0.53    sK7 != k2_mcart_1(k1_mcart_1(sK4)) | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(trivial_inequality_removal,[],[f81])).
% 1.25/0.53  fof(f81,plain,(
% 1.25/0.53    sK6 != sK6 | sK7 != k2_mcart_1(k1_mcart_1(sK4)) | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(backward_demodulation,[],[f74,f80])).
% 1.25/0.53  fof(f80,plain,(
% 1.25/0.53    sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 1.25/0.53    inference(backward_demodulation,[],[f57,f79])).
% 1.25/0.53  fof(f79,plain,(
% 1.25/0.53    sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f78,f14])).
% 1.25/0.53  fof(f78,plain,(
% 1.25/0.53    k1_xboole_0 = sK0 | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f77,f17])).
% 1.25/0.53  fof(f77,plain,(
% 1.25/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f76,f16])).
% 1.25/0.53  fof(f76,plain,(
% 1.25/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f75,f15])).
% 1.25/0.53  fof(f75,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(resolution,[],[f43,f29])).
% 1.25/0.53  fof(f43,plain,(
% 1.25/0.53    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),X7)) | k1_xboole_0 = X5 | k1_xboole_0 = X6 | k1_xboole_0 = X7 | k1_xboole_0 = X4 | sK6 = k9_mcart_1(X4,X5,X6,X7,sK4)) )),
% 1.25/0.53    inference(superposition,[],[f40,f12])).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X6) )),
% 1.25/0.53    inference(equality_resolution,[],[f36])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 1.25/0.53    inference(definition_unfolding,[],[f25,f28])).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 1.25/0.53    inference(cnf_transformation,[],[f10])).
% 1.25/0.53  fof(f57,plain,(
% 1.25/0.53    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 1.25/0.53    inference(subsumption_resolution,[],[f56,f14])).
% 1.25/0.53  fof(f56,plain,(
% 1.25/0.53    k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 1.25/0.53    inference(subsumption_resolution,[],[f55,f17])).
% 1.25/0.53  fof(f55,plain,(
% 1.25/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 1.25/0.53    inference(subsumption_resolution,[],[f54,f16])).
% 1.25/0.53  fof(f54,plain,(
% 1.25/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 1.25/0.53    inference(subsumption_resolution,[],[f47,f15])).
% 1.25/0.53  fof(f47,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 1.25/0.53    inference(resolution,[],[f29,f32])).
% 1.25/0.53  fof(f32,plain,(
% 1.25/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f21,f28])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f9])).
% 1.25/0.53  fof(f74,plain,(
% 1.25/0.53    sK7 != k2_mcart_1(k1_mcart_1(sK4)) | sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(forward_demodulation,[],[f73,f61])).
% 1.25/0.53  fof(f73,plain,(
% 1.25/0.53    sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(forward_demodulation,[],[f72,f57])).
% 1.25/0.53  fof(f72,plain,(
% 1.25/0.53    sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f11,f70])).
% 1.25/0.53  fof(f70,plain,(
% 1.25/0.53    sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f69,f14])).
% 1.25/0.53  fof(f69,plain,(
% 1.25/0.53    k1_xboole_0 = sK0 | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f68,f17])).
% 1.25/0.53  fof(f68,plain,(
% 1.25/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f67,f16])).
% 1.25/0.53  fof(f67,plain,(
% 1.25/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f66,f15])).
% 1.25/0.53  fof(f66,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(resolution,[],[f42,f29])).
% 1.25/0.53  fof(f42,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4)) )),
% 1.25/0.53    inference(superposition,[],[f41,f12])).
% 1.25/0.53  fof(f41,plain,(
% 1.25/0.53    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X5) )),
% 1.25/0.53    inference(equality_resolution,[],[f37])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 1.25/0.53    inference(definition_unfolding,[],[f24,f28])).
% 1.25/0.53  fof(f24,plain,(
% 1.25/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 1.25/0.53    inference(cnf_transformation,[],[f10])).
% 1.25/0.53  fof(f11,plain,(
% 1.25/0.53    sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f96,plain,(
% 1.25/0.53    sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f95,f14])).
% 1.25/0.53  fof(f95,plain,(
% 1.25/0.53    k1_xboole_0 = sK0 | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f94,f17])).
% 1.25/0.53  fof(f94,plain,(
% 1.25/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f93,f16])).
% 1.25/0.53  fof(f93,plain,(
% 1.25/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(subsumption_resolution,[],[f92,f15])).
% 1.25/0.53  fof(f92,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 1.25/0.53    inference(resolution,[],[f45,f29])).
% 1.25/0.53  fof(f45,plain,(
% 1.25/0.53    ( ! [X14,X12,X15,X13] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14),X15)) | k1_xboole_0 = X13 | k1_xboole_0 = X14 | k1_xboole_0 = X15 | k1_xboole_0 = X12 | sK8 = k11_mcart_1(X12,X13,X14,X15,sK4)) )),
% 1.25/0.53    inference(superposition,[],[f38,f12])).
% 1.25/0.53  fof(f38,plain,(
% 1.25/0.53    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8) )),
% 1.25/0.53    inference(equality_resolution,[],[f34])).
% 1.25/0.53  fof(f34,plain,(
% 1.25/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 1.25/0.53    inference(definition_unfolding,[],[f27,f28])).
% 1.25/0.53  fof(f27,plain,(
% 1.25/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 1.25/0.53    inference(cnf_transformation,[],[f10])).
% 1.25/0.53  % (19066)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.53  % SZS output end Proof for theBenchmark
% 1.25/0.53  % (19073)------------------------------
% 1.25/0.53  % (19073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (19073)Termination reason: Refutation
% 1.25/0.53  
% 1.25/0.53  % (19073)Memory used [KB]: 1791
% 1.25/0.53  % (19073)Time elapsed: 0.053 s
% 1.25/0.53  % (19073)------------------------------
% 1.25/0.53  % (19073)------------------------------
% 1.25/0.53  % (19051)Success in time 0.159 s
%------------------------------------------------------------------------------
