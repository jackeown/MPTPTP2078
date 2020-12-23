%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:42 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 219 expanded)
%              Number of leaves         :    4 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  254 (1330 expanded)
%              Number of equality atoms :  230 (1201 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(subsumption_resolution,[],[f75,f65])).

fof(f65,plain,(
    sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f64,f49])).

fof(f49,plain,(
    sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f48,f12])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f48,plain,
    ( k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f47,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f46,f14])).

fof(f14,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f45,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f44,f11])).

fof(f11,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | sK7 = k10_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f29,f23])).

fof(f23,plain,(
    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8) ),
    inference(definition_unfolding,[],[f10,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f10,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X7 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f64,plain,
    ( sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f63])).

fof(f63,plain,
    ( sK6 != sK6
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f41,f62])).

fof(f62,plain,(
    sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f61,f12])).

fof(f61,plain,
    ( k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f60,f15])).

fof(f60,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f59,f14])).

fof(f59,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f58,f13])).

fof(f58,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f57,f11])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | sK6 = k9_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f30,f23])).

fof(f30,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,
    ( sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f40])).

fof(f40,plain,
    ( sK8 != sK8
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(superposition,[],[f9,f39])).

fof(f39,plain,(
    sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f38,f12])).

fof(f38,plain,
    ( k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f37,f15])).

fof(f37,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f36,f14])).

fof(f36,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f35,f13])).

fof(f35,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f34,f11])).

% (28525)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | sK8 = k11_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f28,f23])).

fof(f28,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,plain,
    ( sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,(
    sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f74,f12])).

fof(f74,plain,
    ( k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f73,f15])).

fof(f73,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f72,f14])).

fof(f72,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subsumption_resolution,[],[f71,f13])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f70,f11])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4) ) ),
    inference(superposition,[],[f31,f23])).

fof(f31,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:29:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.47  % (28526)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.48  % (28518)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.48  % (28527)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.48  % (28527)Refutation not found, incomplete strategy% (28527)------------------------------
% 0.18/0.48  % (28527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (28518)Refutation found. Thanks to Tanya!
% 0.18/0.48  % SZS status Theorem for theBenchmark
% 0.18/0.48  % (28517)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.48  % SZS output start Proof for theBenchmark
% 0.18/0.48  fof(f76,plain,(
% 0.18/0.48    $false),
% 0.18/0.48    inference(subsumption_resolution,[],[f75,f65])).
% 0.18/0.48  fof(f65,plain,(
% 0.18/0.48    sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f64,f49])).
% 0.18/0.48  fof(f49,plain,(
% 0.18/0.48    sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f48,f12])).
% 0.18/0.48  fof(f12,plain,(
% 0.18/0.48    k1_xboole_0 != sK0),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f7,plain,(
% 0.18/0.48    ? [X0,X1,X2,X3,X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.18/0.48    inference(flattening,[],[f6])).
% 0.18/0.48  fof(f6,plain,(
% 0.18/0.48    ? [X0,X1,X2,X3,X4] : ((? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.18/0.48    inference(ennf_transformation,[],[f5])).
% 0.18/0.48  fof(f5,negated_conjecture,(
% 0.18/0.48    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.18/0.48    inference(negated_conjecture,[],[f4])).
% 0.18/0.48  fof(f4,conjecture,(
% 0.18/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.18/0.48  fof(f48,plain,(
% 0.18/0.48    k1_xboole_0 = sK0 | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f47,f15])).
% 0.18/0.48  fof(f15,plain,(
% 0.18/0.48    k1_xboole_0 != sK3),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f47,plain,(
% 0.18/0.48    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f46,f14])).
% 0.18/0.48  fof(f14,plain,(
% 0.18/0.48    k1_xboole_0 != sK2),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f46,plain,(
% 0.18/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f45,f13])).
% 0.18/0.48  fof(f13,plain,(
% 0.18/0.48    k1_xboole_0 != sK1),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f45,plain,(
% 0.18/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(resolution,[],[f44,f11])).
% 0.18/0.48  fof(f11,plain,(
% 0.18/0.48    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f44,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | sK7 = k10_mcart_1(X0,X1,X2,X3,sK4)) )),
% 0.18/0.48    inference(superposition,[],[f29,f23])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8)),
% 0.18/0.48    inference(definition_unfolding,[],[f10,f22])).
% 0.18/0.48  fof(f22,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.18/0.48    inference(definition_unfolding,[],[f17,f16])).
% 0.18/0.48  fof(f16,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f1])).
% 0.18/0.48  fof(f1,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.18/0.48  fof(f17,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f2])).
% 0.18/0.48  fof(f2,axiom,(
% 0.18/0.48    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.18/0.48  fof(f10,plain,(
% 0.18/0.48    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f29,plain,(
% 0.18/0.48    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k10_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X7) )),
% 0.18/0.48    inference(equality_resolution,[],[f25])).
% 0.18/0.48  fof(f25,plain,(
% 0.18/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.18/0.48    inference(definition_unfolding,[],[f20,f22])).
% 0.18/0.48  fof(f20,plain,(
% 0.18/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.18/0.48    inference(cnf_transformation,[],[f8])).
% 0.18/0.48  fof(f8,plain,(
% 0.18/0.48    ! [X0,X1,X2,X3] : (! [X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.18/0.48    inference(ennf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,axiom,(
% 0.18/0.48    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).
% 0.18/0.48  fof(f64,plain,(
% 0.18/0.48    sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(trivial_inequality_removal,[],[f63])).
% 0.18/0.48  fof(f63,plain,(
% 0.18/0.48    sK6 != sK6 | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(backward_demodulation,[],[f41,f62])).
% 0.18/0.48  fof(f62,plain,(
% 0.18/0.48    sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f61,f12])).
% 0.18/0.48  fof(f61,plain,(
% 0.18/0.48    k1_xboole_0 = sK0 | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f60,f15])).
% 0.18/0.48  fof(f60,plain,(
% 0.18/0.48    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f59,f14])).
% 0.18/0.48  fof(f59,plain,(
% 0.18/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f58,f13])).
% 0.18/0.48  fof(f58,plain,(
% 0.18/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(resolution,[],[f57,f11])).
% 0.18/0.48  fof(f57,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | sK6 = k9_mcart_1(X0,X1,X2,X3,sK4)) )),
% 0.18/0.48    inference(superposition,[],[f30,f23])).
% 0.18/0.48  fof(f30,plain,(
% 0.18/0.48    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k9_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X6) )),
% 0.18/0.48    inference(equality_resolution,[],[f26])).
% 0.18/0.48  fof(f26,plain,(
% 0.18/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 0.18/0.48    inference(definition_unfolding,[],[f19,f22])).
% 0.18/0.48  fof(f19,plain,(
% 0.18/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 0.18/0.48    inference(cnf_transformation,[],[f8])).
% 0.18/0.48  fof(f41,plain,(
% 0.18/0.48    sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(trivial_inequality_removal,[],[f40])).
% 0.18/0.48  fof(f40,plain,(
% 0.18/0.48    sK8 != sK8 | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(superposition,[],[f9,f39])).
% 0.18/0.48  fof(f39,plain,(
% 0.18/0.48    sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f38,f12])).
% 0.18/0.48  fof(f38,plain,(
% 0.18/0.48    k1_xboole_0 = sK0 | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f37,f15])).
% 0.18/0.48  fof(f37,plain,(
% 0.18/0.48    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f36,f14])).
% 0.18/0.48  fof(f36,plain,(
% 0.18/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f35,f13])).
% 0.18/0.48  fof(f35,plain,(
% 0.18/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(resolution,[],[f34,f11])).
% 0.18/0.48  % (28525)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.48  fof(f34,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | sK8 = k11_mcart_1(X0,X1,X2,X3,sK4)) )),
% 0.18/0.48    inference(superposition,[],[f28,f23])).
% 0.18/0.48  fof(f28,plain,(
% 0.18/0.48    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k11_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X8) )),
% 0.18/0.48    inference(equality_resolution,[],[f24])).
% 0.18/0.48  fof(f24,plain,(
% 0.18/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 0.18/0.48    inference(definition_unfolding,[],[f21,f22])).
% 0.18/0.48  fof(f21,plain,(
% 0.18/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 0.18/0.48    inference(cnf_transformation,[],[f8])).
% 0.18/0.48  fof(f9,plain,(
% 0.18/0.48    sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f75,plain,(
% 0.18/0.48    sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f74,f12])).
% 0.18/0.48  fof(f74,plain,(
% 0.18/0.48    k1_xboole_0 = sK0 | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f73,f15])).
% 0.18/0.48  fof(f73,plain,(
% 0.18/0.48    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f72,f14])).
% 0.18/0.48  fof(f72,plain,(
% 0.18/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f71,f13])).
% 0.18/0.48  fof(f71,plain,(
% 0.18/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.18/0.48    inference(resolution,[],[f70,f11])).
% 0.18/0.48  fof(f70,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | sK5 = k8_mcart_1(X0,X1,X2,X3,sK4)) )),
% 0.18/0.48    inference(superposition,[],[f31,f23])).
% 0.18/0.48  fof(f31,plain,(
% 0.18/0.48    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5) )),
% 0.18/0.48    inference(equality_resolution,[],[f27])).
% 0.18/0.48  fof(f27,plain,(
% 0.18/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 0.18/0.48    inference(definition_unfolding,[],[f18,f22])).
% 0.18/0.48  fof(f18,plain,(
% 0.18/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 0.18/0.48    inference(cnf_transformation,[],[f8])).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (28518)------------------------------
% 0.18/0.48  % (28518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (28518)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (28518)Memory used [KB]: 6268
% 0.18/0.48  % (28518)Time elapsed: 0.092 s
% 0.18/0.48  % (28518)------------------------------
% 0.18/0.48  % (28518)------------------------------
% 0.18/0.48  % (28535)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.49  % (28511)Success in time 0.143 s
%------------------------------------------------------------------------------
