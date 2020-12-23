%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0899+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:51 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 150 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  303 (1041 expanded)
%              Number of equality atoms :  222 ( 885 expanded)
%              Maximal formula depth    :   20 (  10 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f24,f23,f26,f25,f22,f72,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | sK6 = k9_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f73,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,sK4),X1)
      | sK6 = k9_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f50,f21])).

fof(f21,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5,X6,X7,X8] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
                | k10_mcart_1(X0,X1,X2,X3,X4) != X7
                | k9_mcart_1(X0,X1,X2,X3,X4) != X6
                | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f50,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X1)
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
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_mcart_1)).

fof(f72,plain,(
    sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f70])).

% (17271)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f70,plain,
    ( sK5 != sK5
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f68,f69])).

fof(f69,plain,(
    sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f24,f23,f26,f25,f22,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f63,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,sK4),X0)
      | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f48,f21])).

fof(f48,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X0)
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) = X6 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X0)
      | X5 = X6
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) != X5 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_mcart_1)).

fof(f68,plain,
    ( sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( sK8 != sK8
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f60,f65])).

fof(f65,plain,(
    sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f24,f23,f26,f25,f22,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | sK8 = k11_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,sK4),X3)
      | sK8 = k11_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f46,f21])).

fof(f46,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X3)
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) = X9 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X3)
      | X5 = X9
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) != X5 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_mcart_1)).

fof(f60,plain,
    ( sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f59])).

fof(f59,plain,
    ( sK7 != sK7
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f20,f57])).

fof(f57,plain,(
    sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f24,f23,f26,f25,f22,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | sK7 = k10_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f55,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,sK4),X2)
      | sK7 = k10_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f44,f21])).

fof(f44,plain,(
    ! [X6,X2,X0,X8,X7,X3,X1,X9] :
      ( ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)),X2)
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) = X8 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_mcart_1(X6,X7,X8,X9),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,X2)
      | X5 = X8
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X6,X7,X8,X9)) != X5 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_mcart_1)).

fof(f20,plain,
    ( sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
