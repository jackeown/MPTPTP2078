%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:32 EST 2020

% Result     : Theorem 2.30s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  135 (1678 expanded)
%              Number of leaves         :   14 ( 448 expanded)
%              Depth                    :   40
%              Number of atoms          :  220 (5388 expanded)
%              Number of equality atoms :  190 (5155 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3675,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3674,f3486])).

fof(f3486,plain,(
    sK1 != sK3 ),
    inference(trivial_inequality_removal,[],[f3291])).

fof(f3291,plain,
    ( sK0 != sK0
    | sK1 != sK3 ),
    inference(backward_demodulation,[],[f40,f3289])).

fof(f3289,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f3279,f1945])).

fof(f1945,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f1944,f39])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f1944,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f1911])).

fof(f1911,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f41,f1869])).

fof(f1869,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(backward_demodulation,[],[f137,f1868])).

fof(f1868,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) ),
    inference(forward_demodulation,[],[f1867,f274])).

fof(f274,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f141,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f141,plain,(
    ! [X1] : r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f57,f67])).

fof(f67,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) ),
    inference(superposition,[],[f49,f37])).

fof(f37,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1867,plain,(
    k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) = k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f516,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f516,plain,(
    r1_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f504,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f504,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK2) ),
    inference(superposition,[],[f70,f137])).

fof(f70,plain,(
    ! [X6,X7] :
      ( r1_xboole_0(k2_zfmisc_1(X6,X7),k2_zfmisc_1(sK0,sK1))
      | ~ r1_xboole_0(X6,sK2) ) ),
    inference(superposition,[],[f55,f37])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f137,plain,(
    k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f67,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f3279,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK2)
    | sK0 = sK2 ),
    inference(superposition,[],[f52,f3196])).

fof(f3196,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f3162,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3162,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f579,f3147])).

fof(f3147,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f3146,f38])).

fof(f38,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f3146,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f3110])).

fof(f3110,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f41,f2619])).

fof(f2619,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f2618,f62])).

fof(f2618,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2617,f1527])).

fof(f1527,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(subsumption_resolution,[],[f1526,f38])).

fof(f1526,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(trivial_inequality_removal,[],[f1493])).

fof(f1493,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f41,f1123])).

fof(f1123,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f1013,f1122])).

fof(f1122,plain,(
    k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3) ),
    inference(forward_demodulation,[],[f1121,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1121,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3) ),
    inference(forward_demodulation,[],[f1103,f131])).

fof(f131,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k1_xboole_0,sK2),sK3) ),
    inference(forward_demodulation,[],[f121,f99])).

fof(f99,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f91,f50])).

fof(f91,plain,(
    r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f81,f58])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(superposition,[],[f70,f62])).

fof(f121,plain,(
    k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(k1_xboole_0,sK2),sK3) ),
    inference(superposition,[],[f66,f63])).

fof(f63,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X1] : k2_zfmisc_1(k4_xboole_0(X1,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f48,f37])).

fof(f1103,plain,(
    k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(k1_xboole_0,sK2),sK3)) ),
    inference(superposition,[],[f1093,f63])).

fof(f1093,plain,(
    ! [X5] : k4_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(k4_xboole_0(X5,sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(X5,sK2),sK3) ),
    inference(backward_demodulation,[],[f130,f1092])).

fof(f1092,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1053,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1053,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,sK2)),sK3) ),
    inference(superposition,[],[f130,f48])).

fof(f130,plain,(
    ! [X5] : k3_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(k4_xboole_0(X5,sK2),sK3)) ),
    inference(superposition,[],[f53,f66])).

fof(f1013,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3) ),
    inference(forward_demodulation,[],[f1012,f144])).

fof(f144,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3)) ),
    inference(forward_demodulation,[],[f134,f49])).

fof(f134,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3)) ),
    inference(superposition,[],[f67,f37])).

fof(f1012,plain,(
    k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3)) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3) ),
    inference(forward_demodulation,[],[f1011,f67])).

fof(f1011,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3) ),
    inference(forward_demodulation,[],[f1002,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1002,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,k1_xboole_0),sK3) ),
    inference(superposition,[],[f981,f46])).

fof(f981,plain,(
    ! [X5] : k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK2,X5),sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,X5),sK3) ),
    inference(backward_demodulation,[],[f111,f980])).

fof(f980,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3)) ),
    inference(forward_demodulation,[],[f967,f53])).

fof(f967,plain,(
    ! [X1] : k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3)) ),
    inference(superposition,[],[f111,f65])).

fof(f65,plain,(
    ! [X0] : k2_zfmisc_1(k4_xboole_0(sK2,X0),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) ),
    inference(superposition,[],[f48,f37])).

fof(f111,plain,(
    ! [X5] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X5,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK2,X5),sK3)) ),
    inference(superposition,[],[f53,f65])).

fof(f2617,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f2616,f49])).

fof(f2616,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f2574,f104])).

fof(f104,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f65,f49])).

fof(f2574,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f65,f2393])).

fof(f2393,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f2392,f37])).

fof(f2392,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f2391,f2207])).

fof(f2207,plain,(
    sK3 = k3_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f2206,f46])).

fof(f2206,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f2196,f54])).

fof(f2196,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f53,f2115])).

fof(f2115,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f2114,f38])).

fof(f2114,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f2081])).

fof(f2081,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f41,f1972])).

fof(f1972,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) ),
    inference(forward_demodulation,[],[f1946,f63])).

fof(f1946,plain,(
    k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) ),
    inference(backward_demodulation,[],[f123,f1945])).

fof(f123,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK3) ),
    inference(superposition,[],[f66,f49])).

fof(f2391,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f2371,f46])).

fof(f2371,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k1_xboole_0) ),
    inference(superposition,[],[f2353,f1125])).

fof(f1125,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3)) ),
    inference(backward_demodulation,[],[f144,f1123])).

fof(f2353,plain,(
    ! [X5] : k4_xboole_0(k2_zfmisc_1(sK2,X5),k2_zfmisc_1(sK2,k4_xboole_0(X5,sK3))) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X5)) ),
    inference(backward_demodulation,[],[f1391,f2347])).

fof(f2347,plain,(
    ! [X1] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X1)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X1)) ),
    inference(backward_demodulation,[],[f1390,f2346])).

fof(f2346,plain,(
    ! [X4,X3] : k3_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK2,X4)) = k2_zfmisc_1(sK0,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f47,f2080])).

fof(f2080,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f2072,f46])).

fof(f2072,plain,(
    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f53,f1945])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f1390,plain,(
    ! [X1] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) ),
    inference(forward_demodulation,[],[f1377,f53])).

fof(f1377,plain,(
    ! [X1] : k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) ),
    inference(superposition,[],[f143,f67])).

fof(f143,plain,(
    ! [X5] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X5)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,X5))) ),
    inference(superposition,[],[f53,f67])).

fof(f1391,plain,(
    ! [X5] : k4_xboole_0(k2_zfmisc_1(sK2,X5),k2_zfmisc_1(sK2,k4_xboole_0(X5,sK3))) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,X5)) ),
    inference(backward_demodulation,[],[f185,f1390])).

fof(f185,plain,(
    ! [X5] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X5)) = k4_xboole_0(k2_zfmisc_1(sK2,X5),k2_zfmisc_1(sK2,k4_xboole_0(X5,sK3))) ),
    inference(forward_demodulation,[],[f180,f54])).

fof(f180,plain,(
    ! [X5] : k3_xboole_0(k2_zfmisc_1(sK2,X5),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK2,X5),k2_zfmisc_1(sK2,k4_xboole_0(X5,sK3))) ),
    inference(superposition,[],[f53,f68])).

fof(f68,plain,(
    ! [X3] : k2_zfmisc_1(sK2,k4_xboole_0(X3,sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f49,f37])).

fof(f579,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3))
    | k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f558,f39])).

fof(f558,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3))
    | k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f41,f171])).

fof(f171,plain,(
    k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f68,f48])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f40,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f3674,plain,(
    sK1 = sK3 ),
    inference(backward_demodulation,[],[f2207,f3673])).

fof(f3673,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f3669,f46])).

fof(f3669,plain,(
    k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f53,f3147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:02:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (28320)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (28327)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (28335)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (28319)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (28323)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (28322)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (28329)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (28341)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (28333)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.33/0.54  % (28324)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.54  % (28335)Refutation not found, incomplete strategy% (28335)------------------------------
% 1.33/0.54  % (28335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (28335)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (28335)Memory used [KB]: 10618
% 1.33/0.54  % (28335)Time elapsed: 0.129 s
% 1.33/0.54  % (28335)------------------------------
% 1.33/0.54  % (28335)------------------------------
% 1.33/0.54  % (28321)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.33/0.54  % (28325)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.54  % (28330)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.33/0.54  % (28346)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.55  % (28340)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.33/0.55  % (28331)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.55  % (28338)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.55  % (28345)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.55  % (28343)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.55  % (28336)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.55  % (28342)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.55  % (28337)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.55  % (28332)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.33/0.55  % (28328)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.44/0.56  % (28334)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.44/0.56  % (28348)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.56  % (28348)Refutation not found, incomplete strategy% (28348)------------------------------
% 1.44/0.56  % (28348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (28348)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (28348)Memory used [KB]: 1663
% 1.44/0.56  % (28348)Time elapsed: 0.150 s
% 1.44/0.56  % (28348)------------------------------
% 1.44/0.56  % (28348)------------------------------
% 1.44/0.56  % (28339)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.44/0.56  % (28344)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.56  % (28326)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.44/0.57  % (28347)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.99/0.65  % (28373)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.99/0.67  % (28378)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.30/0.69  % (28333)Refutation found. Thanks to Tanya!
% 2.30/0.69  % SZS status Theorem for theBenchmark
% 2.30/0.71  % SZS output start Proof for theBenchmark
% 2.30/0.71  fof(f3675,plain,(
% 2.30/0.71    $false),
% 2.30/0.71    inference(subsumption_resolution,[],[f3674,f3486])).
% 2.30/0.71  fof(f3486,plain,(
% 2.30/0.71    sK1 != sK3),
% 2.30/0.71    inference(trivial_inequality_removal,[],[f3291])).
% 2.30/0.71  fof(f3291,plain,(
% 2.30/0.71    sK0 != sK0 | sK1 != sK3),
% 2.30/0.71    inference(backward_demodulation,[],[f40,f3289])).
% 2.30/0.71  fof(f3289,plain,(
% 2.30/0.71    sK0 = sK2),
% 2.30/0.71    inference(subsumption_resolution,[],[f3279,f1945])).
% 2.30/0.71  fof(f1945,plain,(
% 2.30/0.71    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 2.30/0.71    inference(subsumption_resolution,[],[f1944,f39])).
% 2.30/0.71  fof(f39,plain,(
% 2.30/0.71    k1_xboole_0 != sK1),
% 2.30/0.71    inference(cnf_transformation,[],[f29])).
% 2.30/0.71  fof(f29,plain,(
% 2.30/0.71    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 2.30/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f28])).
% 2.30/0.71  fof(f28,plain,(
% 2.30/0.71    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 2.30/0.71    introduced(choice_axiom,[])).
% 2.30/0.71  fof(f21,plain,(
% 2.30/0.71    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 2.30/0.71    inference(flattening,[],[f20])).
% 2.30/0.71  fof(f20,plain,(
% 2.30/0.71    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 2.30/0.71    inference(ennf_transformation,[],[f17])).
% 2.30/0.71  fof(f17,negated_conjecture,(
% 2.30/0.71    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.30/0.71    inference(negated_conjecture,[],[f16])).
% 2.30/0.71  fof(f16,conjecture,(
% 2.30/0.71    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 2.30/0.71  fof(f1944,plain,(
% 2.30/0.71    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 2.30/0.71    inference(trivial_inequality_removal,[],[f1911])).
% 2.30/0.71  fof(f1911,plain,(
% 2.30/0.71    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 2.30/0.71    inference(superposition,[],[f41,f1869])).
% 2.30/0.71  fof(f1869,plain,(
% 2.30/0.71    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 2.30/0.71    inference(backward_demodulation,[],[f137,f1868])).
% 2.30/0.71  fof(f1868,plain,(
% 2.30/0.71    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))),
% 2.30/0.71    inference(forward_demodulation,[],[f1867,f274])).
% 2.30/0.71  fof(f274,plain,(
% 2.30/0.71    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1))) )),
% 2.30/0.71    inference(resolution,[],[f141,f44])).
% 2.30/0.71  fof(f44,plain,(
% 2.30/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f22])).
% 2.30/0.71  fof(f22,plain,(
% 2.30/0.71    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 2.30/0.71    inference(ennf_transformation,[],[f19])).
% 2.30/0.71  fof(f19,plain,(
% 2.30/0.71    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 2.30/0.71    inference(unused_predicate_definition_removal,[],[f5])).
% 2.30/0.71  fof(f5,axiom,(
% 2.30/0.71    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.30/0.71  fof(f141,plain,(
% 2.30/0.71    ( ! [X1] : (r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X1)),k2_zfmisc_1(sK0,sK1))) )),
% 2.30/0.71    inference(superposition,[],[f57,f67])).
% 2.30/0.71  fof(f67,plain,(
% 2.30/0.71    ( ! [X2] : (k2_zfmisc_1(sK2,k4_xboole_0(sK3,X2)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2))) )),
% 2.30/0.71    inference(superposition,[],[f49,f37])).
% 2.30/0.71  fof(f37,plain,(
% 2.30/0.71    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 2.30/0.71    inference(cnf_transformation,[],[f29])).
% 2.30/0.71  fof(f49,plain,(
% 2.30/0.71    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.30/0.71    inference(cnf_transformation,[],[f14])).
% 2.30/0.71  fof(f14,axiom,(
% 2.30/0.71    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 2.30/0.71  fof(f57,plain,(
% 2.30/0.71    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f7])).
% 2.30/0.71  fof(f7,axiom,(
% 2.30/0.71    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.30/0.71  fof(f1867,plain,(
% 2.30/0.71    k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) = k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1))),
% 2.30/0.71    inference(resolution,[],[f516,f50])).
% 2.30/0.71  fof(f50,plain,(
% 2.30/0.71    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.30/0.71    inference(cnf_transformation,[],[f34])).
% 2.30/0.71  fof(f34,plain,(
% 2.30/0.71    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.30/0.71    inference(nnf_transformation,[],[f11])).
% 2.30/0.71  fof(f11,axiom,(
% 2.30/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.30/0.71  fof(f516,plain,(
% 2.30/0.71    r1_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1))),
% 2.30/0.71    inference(subsumption_resolution,[],[f504,f58])).
% 2.30/0.71  fof(f58,plain,(
% 2.30/0.71    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f10])).
% 2.30/0.71  fof(f10,axiom,(
% 2.30/0.71    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.30/0.71  fof(f504,plain,(
% 2.30/0.71    r1_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)),k2_zfmisc_1(sK0,sK1)) | ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK2)),
% 2.30/0.71    inference(superposition,[],[f70,f137])).
% 2.30/0.71  fof(f70,plain,(
% 2.30/0.71    ( ! [X6,X7] : (r1_xboole_0(k2_zfmisc_1(X6,X7),k2_zfmisc_1(sK0,sK1)) | ~r1_xboole_0(X6,sK2)) )),
% 2.30/0.71    inference(superposition,[],[f55,f37])).
% 2.30/0.71  fof(f55,plain,(
% 2.30/0.71    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f25])).
% 2.30/0.71  fof(f25,plain,(
% 2.30/0.71    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 2.30/0.71    inference(ennf_transformation,[],[f15])).
% 2.30/0.71  fof(f15,axiom,(
% 2.30/0.71    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 2.30/0.71  fof(f137,plain,(
% 2.30/0.71    k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))),
% 2.30/0.71    inference(superposition,[],[f67,f48])).
% 2.30/0.71  fof(f48,plain,(
% 2.30/0.71    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.30/0.71    inference(cnf_transformation,[],[f14])).
% 2.30/0.71  fof(f41,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 2.30/0.71    inference(cnf_transformation,[],[f31])).
% 2.30/0.71  fof(f31,plain,(
% 2.30/0.71    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.30/0.71    inference(flattening,[],[f30])).
% 2.30/0.71  fof(f30,plain,(
% 2.30/0.71    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.30/0.71    inference(nnf_transformation,[],[f12])).
% 2.30/0.71  fof(f12,axiom,(
% 2.30/0.71    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.30/0.71  fof(f3279,plain,(
% 2.30/0.71    k1_xboole_0 != k4_xboole_0(sK0,sK2) | sK0 = sK2),
% 2.30/0.71    inference(superposition,[],[f52,f3196])).
% 2.30/0.71  fof(f3196,plain,(
% 2.30/0.71    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 2.30/0.71    inference(subsumption_resolution,[],[f3162,f62])).
% 2.30/0.71  fof(f62,plain,(
% 2.30/0.71    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.30/0.71    inference(equality_resolution,[],[f43])).
% 2.30/0.71  fof(f43,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.30/0.71    inference(cnf_transformation,[],[f31])).
% 2.30/0.71  fof(f3162,plain,(
% 2.30/0.71    k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 2.30/0.71    inference(backward_demodulation,[],[f579,f3147])).
% 2.30/0.71  fof(f3147,plain,(
% 2.30/0.71    k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 2.30/0.71    inference(subsumption_resolution,[],[f3146,f38])).
% 2.30/0.71  fof(f38,plain,(
% 2.30/0.71    k1_xboole_0 != sK0),
% 2.30/0.71    inference(cnf_transformation,[],[f29])).
% 2.30/0.71  fof(f3146,plain,(
% 2.30/0.71    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 2.30/0.71    inference(trivial_inequality_removal,[],[f3110])).
% 2.30/0.71  fof(f3110,plain,(
% 2.30/0.71    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 2.30/0.71    inference(superposition,[],[f41,f2619])).
% 2.30/0.71  fof(f2619,plain,(
% 2.30/0.71    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 2.30/0.71    inference(forward_demodulation,[],[f2618,f62])).
% 2.30/0.71  fof(f2618,plain,(
% 2.30/0.71    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k1_xboole_0)),
% 2.30/0.71    inference(forward_demodulation,[],[f2617,f1527])).
% 2.30/0.71  fof(f1527,plain,(
% 2.30/0.71    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 2.30/0.71    inference(subsumption_resolution,[],[f1526,f38])).
% 2.30/0.71  fof(f1526,plain,(
% 2.30/0.71    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 2.30/0.71    inference(trivial_inequality_removal,[],[f1493])).
% 2.30/0.71  fof(f1493,plain,(
% 2.30/0.71    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 2.30/0.71    inference(superposition,[],[f41,f1123])).
% 2.30/0.71  fof(f1123,plain,(
% 2.30/0.71    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1))),
% 2.30/0.71    inference(backward_demodulation,[],[f1013,f1122])).
% 2.30/0.71  fof(f1122,plain,(
% 2.30/0.71    k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3)),
% 2.30/0.71    inference(forward_demodulation,[],[f1121,f46])).
% 2.30/0.71  fof(f46,plain,(
% 2.30/0.71    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.30/0.71    inference(cnf_transformation,[],[f8])).
% 2.30/0.71  fof(f8,axiom,(
% 2.30/0.71    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.30/0.71  fof(f1121,plain,(
% 2.30/0.71    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3)),
% 2.30/0.71    inference(forward_demodulation,[],[f1103,f131])).
% 2.30/0.71  fof(f131,plain,(
% 2.30/0.71    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(k1_xboole_0,sK2),sK3)),
% 2.30/0.71    inference(forward_demodulation,[],[f121,f99])).
% 2.30/0.71  fof(f99,plain,(
% 2.30/0.71    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 2.30/0.71    inference(resolution,[],[f91,f50])).
% 2.30/0.71  fof(f91,plain,(
% 2.30/0.71    r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 2.30/0.71    inference(resolution,[],[f81,f58])).
% 2.30/0.71  fof(f81,plain,(
% 2.30/0.71    ( ! [X0] : (~r1_xboole_0(X0,sK2) | r1_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))) )),
% 2.30/0.71    inference(superposition,[],[f70,f62])).
% 2.30/0.71  fof(f121,plain,(
% 2.30/0.71    k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(k1_xboole_0,sK2),sK3)),
% 2.30/0.71    inference(superposition,[],[f66,f63])).
% 2.30/0.71  fof(f63,plain,(
% 2.30/0.71    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.30/0.71    inference(equality_resolution,[],[f42])).
% 2.30/0.71  fof(f42,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.30/0.71    inference(cnf_transformation,[],[f31])).
% 2.30/0.71  fof(f66,plain,(
% 2.30/0.71    ( ! [X1] : (k2_zfmisc_1(k4_xboole_0(X1,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 2.30/0.71    inference(superposition,[],[f48,f37])).
% 2.30/0.71  fof(f1103,plain,(
% 2.30/0.71    k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(k1_xboole_0,sK2),sK3))),
% 2.30/0.71    inference(superposition,[],[f1093,f63])).
% 2.30/0.71  fof(f1093,plain,(
% 2.30/0.71    ( ! [X5] : (k4_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(k4_xboole_0(X5,sK2),sK3)) = k2_zfmisc_1(k3_xboole_0(X5,sK2),sK3)) )),
% 2.30/0.71    inference(backward_demodulation,[],[f130,f1092])).
% 2.30/0.71  fof(f1092,plain,(
% 2.30/0.71    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 2.30/0.71    inference(forward_demodulation,[],[f1053,f53])).
% 2.30/0.71  fof(f53,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.30/0.71    inference(cnf_transformation,[],[f9])).
% 2.30/0.71  fof(f9,axiom,(
% 2.30/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.30/0.71  fof(f1053,plain,(
% 2.30/0.71    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,sK2)),sK3)) )),
% 2.30/0.71    inference(superposition,[],[f130,f48])).
% 2.30/0.71  fof(f130,plain,(
% 2.30/0.71    ( ! [X5] : (k3_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(k4_xboole_0(X5,sK2),sK3))) )),
% 2.30/0.71    inference(superposition,[],[f53,f66])).
% 2.30/0.71  fof(f1013,plain,(
% 2.30/0.71    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3)),
% 2.30/0.71    inference(forward_demodulation,[],[f1012,f144])).
% 2.30/0.71  fof(f144,plain,(
% 2.30/0.71    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3))),
% 2.30/0.71    inference(forward_demodulation,[],[f134,f49])).
% 2.30/0.71  fof(f134,plain,(
% 2.30/0.71    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3))),
% 2.30/0.71    inference(superposition,[],[f67,f37])).
% 2.30/0.71  fof(f1012,plain,(
% 2.30/0.71    k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3)) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3)),
% 2.30/0.71    inference(forward_demodulation,[],[f1011,f67])).
% 2.30/0.71  fof(f1011,plain,(
% 2.30/0.71    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3)),
% 2.30/0.71    inference(forward_demodulation,[],[f1002,f54])).
% 2.30/0.71  fof(f54,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f1])).
% 2.30/0.71  fof(f1,axiom,(
% 2.30/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.30/0.71  fof(f1002,plain,(
% 2.30/0.71    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,k1_xboole_0),sK3)),
% 2.30/0.71    inference(superposition,[],[f981,f46])).
% 2.30/0.71  fof(f981,plain,(
% 2.30/0.71    ( ! [X5] : (k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK2,X5),sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,X5),sK3)) )),
% 2.30/0.71    inference(backward_demodulation,[],[f111,f980])).
% 2.30/0.71  fof(f980,plain,(
% 2.30/0.71    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3))) )),
% 2.30/0.71    inference(forward_demodulation,[],[f967,f53])).
% 2.30/0.71  fof(f967,plain,(
% 2.30/0.71    ( ! [X1] : (k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3))) )),
% 2.30/0.71    inference(superposition,[],[f111,f65])).
% 2.30/0.71  fof(f65,plain,(
% 2.30/0.71    ( ! [X0] : (k2_zfmisc_1(k4_xboole_0(sK2,X0),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))) )),
% 2.30/0.71    inference(superposition,[],[f48,f37])).
% 2.30/0.71  fof(f111,plain,(
% 2.30/0.71    ( ! [X5] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X5,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK2,X5),sK3))) )),
% 2.30/0.71    inference(superposition,[],[f53,f65])).
% 2.30/0.71  fof(f2617,plain,(
% 2.30/0.71    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1))),
% 2.30/0.71    inference(forward_demodulation,[],[f2616,f49])).
% 2.30/0.71  fof(f2616,plain,(
% 2.30/0.71    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 2.30/0.71    inference(forward_demodulation,[],[f2574,f104])).
% 2.30/0.71  fof(f104,plain,(
% 2.30/0.71    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 2.30/0.71    inference(superposition,[],[f65,f49])).
% 2.30/0.71  fof(f2574,plain,(
% 2.30/0.71    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 2.30/0.71    inference(superposition,[],[f65,f2393])).
% 2.30/0.71  fof(f2393,plain,(
% 2.30/0.71    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 2.30/0.71    inference(forward_demodulation,[],[f2392,f37])).
% 2.30/0.71  fof(f2392,plain,(
% 2.30/0.71    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK3)),
% 2.30/0.71    inference(forward_demodulation,[],[f2391,f2207])).
% 2.30/0.71  fof(f2207,plain,(
% 2.30/0.71    sK3 = k3_xboole_0(sK1,sK3)),
% 2.30/0.71    inference(forward_demodulation,[],[f2206,f46])).
% 2.30/0.71  fof(f2206,plain,(
% 2.30/0.71    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK1,sK3)),
% 2.30/0.71    inference(forward_demodulation,[],[f2196,f54])).
% 2.30/0.71  fof(f2196,plain,(
% 2.30/0.71    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,sK1)),
% 2.30/0.71    inference(superposition,[],[f53,f2115])).
% 2.30/0.71  fof(f2115,plain,(
% 2.30/0.71    k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 2.30/0.71    inference(subsumption_resolution,[],[f2114,f38])).
% 2.30/0.71  fof(f2114,plain,(
% 2.30/0.71    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 2.30/0.71    inference(trivial_inequality_removal,[],[f2081])).
% 2.30/0.71  fof(f2081,plain,(
% 2.30/0.71    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 2.30/0.71    inference(superposition,[],[f41,f1972])).
% 2.30/0.71  fof(f1972,plain,(
% 2.30/0.71    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))),
% 2.30/0.71    inference(forward_demodulation,[],[f1946,f63])).
% 2.30/0.71  fof(f1946,plain,(
% 2.30/0.71    k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))),
% 2.30/0.71    inference(backward_demodulation,[],[f123,f1945])).
% 2.30/0.71  fof(f123,plain,(
% 2.30/0.71    k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK3)),
% 2.30/0.71    inference(superposition,[],[f66,f49])).
% 2.30/0.71  fof(f2391,plain,(
% 2.30/0.71    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 2.30/0.71    inference(forward_demodulation,[],[f2371,f46])).
% 2.30/0.71  fof(f2371,plain,(
% 2.30/0.71    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k1_xboole_0)),
% 2.30/0.71    inference(superposition,[],[f2353,f1125])).
% 2.30/0.71  fof(f1125,plain,(
% 2.30/0.71    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3))),
% 2.30/0.71    inference(backward_demodulation,[],[f144,f1123])).
% 2.30/0.71  fof(f2353,plain,(
% 2.30/0.71    ( ! [X5] : (k4_xboole_0(k2_zfmisc_1(sK2,X5),k2_zfmisc_1(sK2,k4_xboole_0(X5,sK3))) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X5))) )),
% 2.30/0.71    inference(backward_demodulation,[],[f1391,f2347])).
% 2.30/0.71  fof(f2347,plain,(
% 2.30/0.71    ( ! [X1] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X1)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X1))) )),
% 2.30/0.71    inference(backward_demodulation,[],[f1390,f2346])).
% 2.30/0.71  fof(f2346,plain,(
% 2.30/0.71    ( ! [X4,X3] : (k3_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK2,X4)) = k2_zfmisc_1(sK0,k3_xboole_0(X3,X4))) )),
% 2.30/0.71    inference(superposition,[],[f47,f2080])).
% 2.30/0.71  fof(f2080,plain,(
% 2.30/0.71    sK0 = k3_xboole_0(sK0,sK2)),
% 2.30/0.71    inference(forward_demodulation,[],[f2072,f46])).
% 2.30/0.71  fof(f2072,plain,(
% 2.30/0.71    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 2.30/0.71    inference(superposition,[],[f53,f1945])).
% 2.30/0.71  fof(f47,plain,(
% 2.30/0.71    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.30/0.71    inference(cnf_transformation,[],[f13])).
% 2.30/0.71  fof(f13,axiom,(
% 2.30/0.71    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 2.30/0.71  fof(f1390,plain,(
% 2.30/0.71    ( ! [X1] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1))) )),
% 2.30/0.71    inference(forward_demodulation,[],[f1377,f53])).
% 2.30/0.71  fof(f1377,plain,(
% 2.30/0.71    ( ! [X1] : (k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1))) )),
% 2.30/0.71    inference(superposition,[],[f143,f67])).
% 2.30/0.71  fof(f143,plain,(
% 2.30/0.71    ( ! [X5] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X5)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,X5)))) )),
% 2.30/0.71    inference(superposition,[],[f53,f67])).
% 2.30/0.71  fof(f1391,plain,(
% 2.30/0.71    ( ! [X5] : (k4_xboole_0(k2_zfmisc_1(sK2,X5),k2_zfmisc_1(sK2,k4_xboole_0(X5,sK3))) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,X5))) )),
% 2.30/0.71    inference(backward_demodulation,[],[f185,f1390])).
% 2.30/0.71  fof(f185,plain,(
% 2.30/0.71    ( ! [X5] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X5)) = k4_xboole_0(k2_zfmisc_1(sK2,X5),k2_zfmisc_1(sK2,k4_xboole_0(X5,sK3)))) )),
% 2.30/0.71    inference(forward_demodulation,[],[f180,f54])).
% 2.30/0.71  fof(f180,plain,(
% 2.30/0.71    ( ! [X5] : (k3_xboole_0(k2_zfmisc_1(sK2,X5),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK2,X5),k2_zfmisc_1(sK2,k4_xboole_0(X5,sK3)))) )),
% 2.30/0.71    inference(superposition,[],[f53,f68])).
% 2.30/0.71  fof(f68,plain,(
% 2.30/0.71    ( ! [X3] : (k2_zfmisc_1(sK2,k4_xboole_0(X3,sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1))) )),
% 2.30/0.71    inference(superposition,[],[f49,f37])).
% 2.30/0.71  fof(f579,plain,(
% 2.30/0.71    k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3)) | k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 2.30/0.71    inference(subsumption_resolution,[],[f558,f39])).
% 2.30/0.71  fof(f558,plain,(
% 2.30/0.71    k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3)) | k1_xboole_0 = k4_xboole_0(sK2,sK0) | k1_xboole_0 = sK1),
% 2.30/0.71    inference(superposition,[],[f41,f171])).
% 2.30/0.71  fof(f171,plain,(
% 2.30/0.71    k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3))),
% 2.30/0.71    inference(superposition,[],[f68,f48])).
% 2.30/0.71  fof(f52,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 2.30/0.71    inference(cnf_transformation,[],[f24])).
% 2.30/0.71  fof(f24,plain,(
% 2.30/0.71    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 2.30/0.71    inference(ennf_transformation,[],[f6])).
% 2.30/0.71  fof(f6,axiom,(
% 2.30/0.71    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 2.30/0.71  fof(f40,plain,(
% 2.30/0.71    sK1 != sK3 | sK0 != sK2),
% 2.30/0.71    inference(cnf_transformation,[],[f29])).
% 2.30/0.71  fof(f3674,plain,(
% 2.30/0.71    sK1 = sK3),
% 2.30/0.71    inference(backward_demodulation,[],[f2207,f3673])).
% 2.30/0.71  fof(f3673,plain,(
% 2.30/0.71    sK1 = k3_xboole_0(sK1,sK3)),
% 2.30/0.71    inference(forward_demodulation,[],[f3669,f46])).
% 2.30/0.71  fof(f3669,plain,(
% 2.30/0.71    k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 2.30/0.71    inference(superposition,[],[f53,f3147])).
% 2.30/0.71  % SZS output end Proof for theBenchmark
% 2.30/0.71  % (28333)------------------------------
% 2.30/0.71  % (28333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.71  % (28333)Termination reason: Refutation
% 2.30/0.71  
% 2.30/0.71  % (28333)Memory used [KB]: 2942
% 2.30/0.71  % (28333)Time elapsed: 0.230 s
% 2.30/0.71  % (28333)------------------------------
% 2.30/0.71  % (28333)------------------------------
% 2.30/0.71  % (28316)Success in time 0.342 s
%------------------------------------------------------------------------------
