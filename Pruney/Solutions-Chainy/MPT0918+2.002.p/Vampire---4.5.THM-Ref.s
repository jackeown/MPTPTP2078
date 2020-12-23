%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 293 expanded)
%              Number of leaves         :    7 (  96 expanded)
%              Depth                    :   19
%              Number of atoms          :  234 (2270 expanded)
%              Number of equality atoms :  219 (2078 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(subsumption_resolution,[],[f67,f70])).

fof(f70,plain,(
    sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(trivial_inequality_removal,[],[f68])).

fof(f68,plain,
    ( sK5 != sK5
    | sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(backward_demodulation,[],[f65,f66])).

fof(f66,plain,(
    sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(superposition,[],[f26,f59])).

fof(f59,plain,(
    k4_tarski(sK5,sK6) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f26,f54])).

fof(f54,plain,(
    k4_tarski(k4_tarski(sK5,sK6),sK7) = k1_mcart_1(sK4) ),
    inference(superposition,[],[f26,f30])).

fof(f30,plain,(
    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8) ),
    inference(definition_unfolding,[],[f19,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f19,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
    & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f9,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4] :
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
        & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( ? [X8,X7,X6,X5] :
          ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
            | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
            | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
            | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X8,X7,X6,X5] :
        ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
          | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
          | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
          | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
        & k4_mcart_1(X5,X6,X7,X8) = sK4 )
   => ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
        | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
        | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
      & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f26,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f65,plain,
    ( sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f64,f57])).

fof(f57,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 ),
    inference(backward_demodulation,[],[f53,f55])).

fof(f55,plain,(
    sK8 = k2_mcart_1(sK4) ),
    inference(superposition,[],[f27,f30])).

fof(f27,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f53,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f52,f15])).

% (25542)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f51,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f50,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f34,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f14,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f14,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,
    ( sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 ),
    inference(trivial_inequality_removal,[],[f62])).

fof(f62,plain,
    ( sK7 != sK7
    | sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 ),
    inference(backward_demodulation,[],[f49,f60])).

fof(f60,plain,(
    sK7 = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f27,f54])).

fof(f49,plain,
    ( sK7 != k2_mcart_1(k1_mcart_1(sK4))
    | sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 ),
    inference(backward_demodulation,[],[f44,f48])).

fof(f48,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f47,f15])).

fof(f47,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f46,f16])).

fof(f46,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f45,f17])).

fof(f45,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f33,f18])).

fof(f33,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f14,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,
    ( sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 ),
    inference(backward_demodulation,[],[f39,f43])).

fof(f43,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f42,f15])).

fof(f42,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f41,f16])).

% (25541)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f41,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f40,f17])).

fof(f40,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f32,f18])).

fof(f32,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f14,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,
    ( sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 ),
    inference(backward_demodulation,[],[f20,f38])).

fof(f38,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(subsumption_resolution,[],[f37,f15])).

fof(f37,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f36,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f35,f17])).

fof(f35,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f31,f18])).

fof(f31,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f14,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    inference(superposition,[],[f27,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:23:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (25549)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (25537)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (25536)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (25536)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (25554)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (25538)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (25558)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f67,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    sK5 != sK5 | sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.53    inference(backward_demodulation,[],[f65,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.53    inference(superposition,[],[f26,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    k4_tarski(sK5,sK6) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.53    inference(superposition,[],[f26,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    k4_tarski(k4_tarski(sK5,sK6),sK7) = k1_mcart_1(sK4)),
% 0.21/0.53    inference(superposition,[],[f26,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8)),
% 0.21/0.53    inference(definition_unfolding,[],[f19,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5) & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f9,f12,f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) => (? [X8,X7,X6,X5] : ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5) & k4_mcart_1(X5,X6,X7,X8) = sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X8,X7,X6,X5] : ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5) & k4_mcart_1(X5,X6,X7,X8) = sK4) => ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5) & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.53    inference(flattening,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4] : ((? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f6])).
% 0.21/0.53  fof(f6,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f64,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8),
% 0.21/0.53    inference(backward_demodulation,[],[f53,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    sK8 = k2_mcart_1(sK4)),
% 0.21/0.53    inference(superposition,[],[f27,f30])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f52,f15])).
% 0.21/0.53  % (25542)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f51,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f50,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    k1_xboole_0 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f34,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    k1_xboole_0 != sK3),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(resolution,[],[f14,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    sK7 != sK7 | sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8),
% 0.21/0.53    inference(backward_demodulation,[],[f49,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    sK7 = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.53    inference(superposition,[],[f27,f54])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    sK7 != k2_mcart_1(k1_mcart_1(sK4)) | sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8),
% 0.21/0.53    inference(backward_demodulation,[],[f44,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.53    inference(subsumption_resolution,[],[f47,f15])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f46,f16])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f45,f17])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f33,f18])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(resolution,[],[f14,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7),
% 0.21/0.53    inference(backward_demodulation,[],[f39,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f42,f15])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f41,f16])).
% 0.21/0.53  % (25541)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f40,f17])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f32,f18])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(resolution,[],[f14,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6),
% 0.21/0.53    inference(backward_demodulation,[],[f20,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f37,f15])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f36,f16])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f35,f17])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f31,f18])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.53    inference(resolution,[],[f14,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.53    inference(superposition,[],[f27,f59])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (25536)------------------------------
% 0.21/0.53  % (25536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25536)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (25536)Memory used [KB]: 1791
% 0.21/0.53  % (25536)Time elapsed: 0.116 s
% 0.21/0.53  % (25536)------------------------------
% 0.21/0.53  % (25536)------------------------------
% 0.21/0.53  % (25535)Success in time 0.171 s
%------------------------------------------------------------------------------
