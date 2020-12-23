%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:30 EST 2020

% Result     : Theorem 10.50s
% Output     : Refutation 10.50s
% Verified   : 
% Statistics : Number of formulae       :  138 (1360 expanded)
%              Number of leaves         :   13 ( 391 expanded)
%              Depth                    :   41
%              Number of atoms          :  253 (3592 expanded)
%              Number of equality atoms :  177 (3293 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12390,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12389,f10665])).

fof(f10665,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f10653,f7087])).

fof(f7087,plain,(
    r1_tarski(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f7083])).

fof(f7083,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2) ),
    inference(backward_demodulation,[],[f4328,f7025])).

fof(f7025,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f6993,f342])).

fof(f342,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1))
      | k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,X1)) ) ),
    inference(superposition,[],[f188,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f188,plain,(
    ! [X0] : k2_zfmisc_1(sK2,k4_xboole_0(sK3,X0)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) ),
    inference(superposition,[],[f61,f37])).

fof(f37,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f25])).

fof(f25,plain,
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

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f6993,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f6960,f37])).

fof(f6960,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1)) ),
    inference(superposition,[],[f3730,f138])).

fof(f138,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f132,f42])).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f132,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f46,f112])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f101,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f101,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f46,f42])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f3730,plain,(
    ! [X32] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X32,sK2),sK3),k2_zfmisc_1(X32,sK1)) ),
    inference(superposition,[],[f111,f1624])).

fof(f1624,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(backward_demodulation,[],[f1213,f1607])).

fof(f1607,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_zfmisc_1(X5,X6),k2_zfmisc_1(k4_xboole_0(X5,X7),X6)) = k2_zfmisc_1(k3_xboole_0(X5,X7),X6) ),
    inference(backward_demodulation,[],[f173,f1606])).

fof(f1606,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4)) = k2_zfmisc_1(k3_xboole_0(X3,X5),X4) ),
    inference(forward_demodulation,[],[f1556,f46])).

fof(f1556,plain,(
    ! [X4,X5,X3] : k2_zfmisc_1(k4_xboole_0(X3,k4_xboole_0(X3,X5)),X4) = k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4)) ),
    inference(superposition,[],[f173,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f173,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k2_zfmisc_1(X5,X6),k2_zfmisc_1(X7,X6)) = k4_xboole_0(k2_zfmisc_1(X5,X6),k2_zfmisc_1(k4_xboole_0(X5,X7),X6)) ),
    inference(superposition,[],[f46,f60])).

fof(f1213,plain,(
    ! [X1] : k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k4_xboole_0(X1,sK2),sK3)) = k3_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(backward_demodulation,[],[f306,f1173])).

fof(f1173,plain,(
    ! [X10,X8,X11,X9] : k3_xboole_0(k2_zfmisc_1(X8,X11),k2_zfmisc_1(X9,X10)) = k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11)) ),
    inference(superposition,[],[f274,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f274,plain,(
    ! [X6,X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4)) = k2_zfmisc_1(k3_xboole_0(X5,X6),k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f64,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f306,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k4_xboole_0(X1,sK2),sK3)) ),
    inference(superposition,[],[f46,f165])).

fof(f165,plain,(
    ! [X0] : k2_zfmisc_1(k4_xboole_0(X0,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f60,f37])).

fof(f111,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(superposition,[],[f44,f46])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f4328,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))
    | r1_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f4315,f39])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f4315,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))
    | r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f350,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f350,plain,(
    ! [X6] :
      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X6))
      | k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK3,X6)) ) ),
    inference(superposition,[],[f55,f188])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10653,plain,
    ( sK1 = sK3
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f10282,f655])).

fof(f655,plain,
    ( ~ r1_tarski(sK1,sK3)
    | sK1 = sK3
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f620,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f620,plain,
    ( r1_tarski(sK3,sK1)
    | ~ r1_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f612,f38])).

fof(f38,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f612,plain,
    ( ~ r1_tarski(sK0,sK2)
    | r1_tarski(sK3,sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f516,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f516,plain,(
    ! [X25] :
      ( r1_tarski(k2_zfmisc_1(X25,sK3),k2_zfmisc_1(sK0,sK1))
      | ~ r1_tarski(X25,sK2) ) ),
    inference(superposition,[],[f266,f113])).

fof(f113,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f102,f42])).

fof(f102,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k4_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f46,f56])).

fof(f266,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X0,sK2),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f252,f45])).

fof(f252,plain,(
    ! [X2] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,X2),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f228,f46])).

fof(f228,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k4_xboole_0(sK2,X0),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f44,f162])).

fof(f162,plain,(
    ! [X0] : k2_zfmisc_1(k4_xboole_0(sK2,X0),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) ),
    inference(superposition,[],[f60,f37])).

fof(f10282,plain,(
    r1_tarski(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f10174])).

fof(f10174,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3) ),
    inference(backward_demodulation,[],[f3976,f10122])).

fof(f10122,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f10121,f112])).

fof(f10121,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f10053,f224])).

fof(f224,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f162,f61])).

fof(f10053,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f162,f8718])).

fof(f8718,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f8717,f37])).

fof(f8717,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f8640,f8409])).

fof(f8409,plain,(
    ! [X9] : k2_zfmisc_1(X9,sK3) = k2_zfmisc_1(X9,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f8408,f45])).

fof(f8408,plain,(
    ! [X9] : k2_zfmisc_1(X9,sK3) = k2_zfmisc_1(X9,k3_xboole_0(sK3,sK1)) ),
    inference(forward_demodulation,[],[f8407,f42])).

fof(f8407,plain,(
    ! [X9] : k2_zfmisc_1(X9,k3_xboole_0(sK3,sK1)) = k4_xboole_0(k2_zfmisc_1(X9,sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f8370,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f8370,plain,(
    ! [X9] : k2_zfmisc_1(X9,k3_xboole_0(sK3,sK1)) = k4_xboole_0(k2_zfmisc_1(X9,sK3),k2_zfmisc_1(X9,k1_xboole_0)) ),
    inference(superposition,[],[f1910,f7737])).

fof(f7737,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f7727,f38])).

fof(f7727,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f7680])).

fof(f7680,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f57,f7338])).

fof(f7338,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) ),
    inference(forward_demodulation,[],[f7250,f68])).

fof(f68,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7250,plain,(
    k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) ),
    inference(backward_demodulation,[],[f301,f7249])).

fof(f7249,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f7232,f39])).

fof(f7232,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f7185])).

fof(f7185,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f57,f7032])).

fof(f7032,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(backward_demodulation,[],[f341,f7025])).

fof(f341,plain,(
    k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f188,f60])).

fof(f301,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK3) ),
    inference(superposition,[],[f165,f61])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1910,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k2_zfmisc_1(X7,X8),k2_zfmisc_1(X7,k4_xboole_0(X8,X9))) = k2_zfmisc_1(X7,k3_xboole_0(X8,X9)) ),
    inference(backward_demodulation,[],[f201,f1909])).

fof(f1909,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(X3,k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f1847,f46])).

fof(f1847,plain,(
    ! [X4,X5,X3] : k2_zfmisc_1(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) ),
    inference(superposition,[],[f201,f61])).

fof(f201,plain,(
    ! [X8,X7,X9] : k3_xboole_0(k2_zfmisc_1(X7,X8),k2_zfmisc_1(X7,X9)) = k4_xboole_0(k2_zfmisc_1(X7,X8),k2_zfmisc_1(X7,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f46,f61])).

fof(f8640,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f8476,f138])).

fof(f8476,plain,(
    ! [X1] : k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X1)) ),
    inference(backward_demodulation,[],[f1928,f8454])).

fof(f8454,plain,(
    ! [X2,X1] : k3_xboole_0(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK2,X2)) = k2_zfmisc_1(sK0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f64,f8207])).

fof(f8207,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f8180,f42])).

fof(f8180,plain,(
    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f46,f7249])).

fof(f1928,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3)) ),
    inference(backward_demodulation,[],[f398,f1910])).

fof(f398,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k4_xboole_0(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(sK2,k4_xboole_0(X1,sK3))) ),
    inference(forward_demodulation,[],[f381,f45])).

fof(f381,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(sK2,k4_xboole_0(X1,sK3))) ),
    inference(superposition,[],[f46,f191])).

fof(f191,plain,(
    ! [X0] : k2_zfmisc_1(sK2,k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f61,f37])).

fof(f3976,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))
    | r1_tarski(sK1,sK3) ),
    inference(forward_demodulation,[],[f3975,f224])).

fof(f3975,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)
    | r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f3966,f38])).

fof(f3966,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)
    | r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f234,f63])).

fof(f234,plain,(
    ! [X6] :
      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X6,sK3))
      | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(sK2,X6),sK3) ) ),
    inference(superposition,[],[f55,f162])).

fof(f12389,plain,(
    sK1 != sK3 ),
    inference(trivial_inequality_removal,[],[f12214])).

fof(f12214,plain,
    ( sK0 != sK0
    | sK1 != sK3 ),
    inference(backward_demodulation,[],[f40,f12213])).

fof(f12213,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f12212,f7087])).

fof(f12212,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f10735,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10735,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(backward_demodulation,[],[f774,f10665])).

fof(f774,plain,
    ( ~ r1_tarski(sK1,sK3)
    | sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f759,f52])).

fof(f759,plain,
    ( r1_tarski(sK2,sK0)
    | ~ r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f752,f39])).

fof(f752,plain,
    ( ~ r1_tarski(sK1,sK3)
    | r1_tarski(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f517,f62])).

fof(f517,plain,(
    ! [X26] :
      ( r1_tarski(k2_zfmisc_1(sK2,X26),k2_zfmisc_1(sK0,sK1))
      | ~ r1_tarski(X26,sK3) ) ),
    inference(superposition,[],[f401,f113])).

fof(f401,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f367,f45])).

fof(f367,plain,(
    ! [X2] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f346,f46])).

fof(f346,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f44,f188])).

fof(f40,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (28818)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (28810)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (28812)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (28817)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (28809)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (28830)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (28819)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (28807)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (28831)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (28822)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (28827)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (28835)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (28820)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (28811)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (28836)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (28825)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (28808)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (28837)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (28837)Refutation not found, incomplete strategy% (28837)------------------------------
% 0.21/0.54  % (28837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28837)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28837)Memory used [KB]: 1663
% 0.21/0.54  % (28837)Time elapsed: 0.137 s
% 0.21/0.54  % (28837)------------------------------
% 0.21/0.54  % (28837)------------------------------
% 0.21/0.54  % (28814)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (28833)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (28813)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (28823)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (28815)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (28828)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (28832)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (28826)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (28834)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (28823)Refutation not found, incomplete strategy% (28823)------------------------------
% 0.21/0.55  % (28823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28821)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (28816)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (28823)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28823)Memory used [KB]: 10618
% 0.21/0.55  % (28823)Time elapsed: 0.111 s
% 0.21/0.55  % (28823)------------------------------
% 0.21/0.55  % (28823)------------------------------
% 0.21/0.56  % (28824)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.05/0.68  % (28928)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.05/0.69  % (28937)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.35/0.80  % (28809)Time limit reached!
% 3.35/0.80  % (28809)------------------------------
% 3.35/0.80  % (28809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.80  % (28809)Termination reason: Time limit
% 3.35/0.80  % (28809)Termination phase: Saturation
% 3.35/0.80  
% 3.35/0.80  % (28809)Memory used [KB]: 6908
% 3.35/0.80  % (28809)Time elapsed: 0.400 s
% 3.35/0.80  % (28809)------------------------------
% 3.35/0.80  % (28809)------------------------------
% 3.35/0.83  % (28832)Time limit reached!
% 3.35/0.83  % (28832)------------------------------
% 3.35/0.83  % (28832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.83  % (28832)Termination reason: Time limit
% 3.35/0.83  
% 3.35/0.83  % (28832)Memory used [KB]: 13432
% 3.35/0.83  % (28832)Time elapsed: 0.426 s
% 3.35/0.83  % (28832)------------------------------
% 3.35/0.83  % (28832)------------------------------
% 4.19/0.90  % (28821)Time limit reached!
% 4.19/0.90  % (28821)------------------------------
% 4.19/0.90  % (28821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/0.90  % (28821)Termination reason: Time limit
% 4.19/0.90  
% 4.19/0.90  % (28821)Memory used [KB]: 4605
% 4.19/0.90  % (28821)Time elapsed: 0.503 s
% 4.19/0.90  % (28821)------------------------------
% 4.19/0.90  % (28821)------------------------------
% 4.19/0.92  % (28813)Time limit reached!
% 4.19/0.92  % (28813)------------------------------
% 4.19/0.92  % (28813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/0.92  % (28813)Termination reason: Time limit
% 4.19/0.92  
% 4.19/0.92  % (28813)Memory used [KB]: 15095
% 4.19/0.92  % (28813)Time elapsed: 0.506 s
% 4.19/0.92  % (28813)------------------------------
% 4.19/0.92  % (28813)------------------------------
% 4.41/0.95  % (29008)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.41/0.97  % (29029)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.41/1.02  % (29033)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.07/1.04  % (29034)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.07/1.08  % (28814)Time limit reached!
% 5.07/1.08  % (28814)------------------------------
% 5.07/1.08  % (28814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.07/1.08  % (28814)Termination reason: Time limit
% 5.07/1.08  % (28814)Termination phase: Saturation
% 5.07/1.08  
% 5.07/1.08  % (28814)Memory used [KB]: 6268
% 5.07/1.08  % (28814)Time elapsed: 0.600 s
% 5.07/1.08  % (28814)------------------------------
% 5.07/1.08  % (28814)------------------------------
% 6.46/1.21  % (28808)Time limit reached!
% 6.46/1.21  % (28808)------------------------------
% 6.46/1.21  % (28808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.63/1.22  % (29035)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.63/1.22  % (28808)Termination reason: Time limit
% 6.63/1.22  
% 6.63/1.22  % (28808)Memory used [KB]: 7675
% 6.63/1.22  % (28808)Time elapsed: 0.806 s
% 6.63/1.22  % (28808)------------------------------
% 6.63/1.22  % (28808)------------------------------
% 7.45/1.32  % (28810)Time limit reached!
% 7.45/1.32  % (28810)------------------------------
% 7.45/1.32  % (28810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.45/1.33  % (28810)Termination reason: Time limit
% 7.45/1.33  
% 7.45/1.33  % (28810)Memory used [KB]: 7419
% 7.45/1.33  % (28810)Time elapsed: 0.916 s
% 7.45/1.33  % (28810)------------------------------
% 7.45/1.33  % (28810)------------------------------
% 7.45/1.36  % (29036)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 8.02/1.43  % (28835)Time limit reached!
% 8.02/1.43  % (28835)------------------------------
% 8.02/1.43  % (28835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.02/1.43  % (28835)Termination reason: Time limit
% 8.02/1.43  % (28835)Termination phase: Saturation
% 8.02/1.43  
% 8.02/1.43  % (28835)Memory used [KB]: 14967
% 8.02/1.43  % (28835)Time elapsed: 1.0000 s
% 8.02/1.43  % (28835)------------------------------
% 8.02/1.43  % (28835)------------------------------
% 8.02/1.44  % (28819)Time limit reached!
% 8.02/1.44  % (28819)------------------------------
% 8.02/1.44  % (28819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.02/1.45  % (29037)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 8.02/1.46  % (28819)Termination reason: Time limit
% 8.02/1.46  
% 8.02/1.46  % (28819)Memory used [KB]: 19445
% 8.02/1.46  % (28819)Time elapsed: 1.029 s
% 8.02/1.46  % (28819)------------------------------
% 8.02/1.46  % (28819)------------------------------
% 9.08/1.57  % (29038)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.08/1.60  % (29039)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.67/1.64  % (28807)Time limit reached!
% 9.67/1.64  % (28807)------------------------------
% 9.67/1.64  % (28807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.67/1.64  % (28807)Termination reason: Time limit
% 9.67/1.64  
% 9.67/1.64  % (28807)Memory used [KB]: 12792
% 9.67/1.64  % (28807)Time elapsed: 1.206 s
% 9.67/1.64  % (28807)------------------------------
% 9.67/1.64  % (28807)------------------------------
% 9.67/1.69  % (29008)Time limit reached!
% 9.67/1.69  % (29008)------------------------------
% 9.67/1.69  % (29008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.67/1.69  % (29008)Termination reason: Time limit
% 9.67/1.69  
% 9.67/1.69  % (29008)Memory used [KB]: 15479
% 9.67/1.69  % (29008)Time elapsed: 0.845 s
% 9.67/1.69  % (29008)------------------------------
% 9.67/1.69  % (29008)------------------------------
% 10.50/1.71  % (28812)Time limit reached!
% 10.50/1.71  % (28812)------------------------------
% 10.50/1.71  % (28812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.50/1.71  % (28812)Termination reason: Time limit
% 10.50/1.71  % (28812)Termination phase: Saturation
% 10.50/1.71  
% 10.50/1.71  % (28812)Memory used [KB]: 14072
% 10.50/1.71  % (28812)Time elapsed: 1.307 s
% 10.50/1.71  % (28812)------------------------------
% 10.50/1.71  % (28812)------------------------------
% 10.50/1.73  % (29035)Time limit reached!
% 10.50/1.73  % (29035)------------------------------
% 10.50/1.73  % (29035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.50/1.73  % (28816)Refutation found. Thanks to Tanya!
% 10.50/1.73  % SZS status Theorem for theBenchmark
% 10.50/1.73  % SZS output start Proof for theBenchmark
% 10.50/1.73  fof(f12390,plain,(
% 10.50/1.73    $false),
% 10.50/1.73    inference(subsumption_resolution,[],[f12389,f10665])).
% 10.50/1.73  fof(f10665,plain,(
% 10.50/1.73    sK1 = sK3),
% 10.50/1.73    inference(subsumption_resolution,[],[f10653,f7087])).
% 10.50/1.73  fof(f7087,plain,(
% 10.50/1.73    r1_tarski(sK0,sK2)),
% 10.50/1.73    inference(trivial_inequality_removal,[],[f7083])).
% 10.50/1.73  fof(f7083,plain,(
% 10.50/1.73    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2)),
% 10.50/1.73    inference(backward_demodulation,[],[f4328,f7025])).
% 10.50/1.73  fof(f7025,plain,(
% 10.50/1.73    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))),
% 10.50/1.73    inference(resolution,[],[f6993,f342])).
% 10.50/1.73  fof(f342,plain,(
% 10.50/1.73    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) | k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,X1))) )),
% 10.50/1.73    inference(superposition,[],[f188,f56])).
% 10.50/1.73  fof(f56,plain,(
% 10.50/1.73    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 10.50/1.73    inference(cnf_transformation,[],[f34])).
% 10.50/1.73  fof(f34,plain,(
% 10.50/1.73    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 10.50/1.73    inference(nnf_transformation,[],[f5])).
% 10.50/1.73  fof(f5,axiom,(
% 10.50/1.73    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 10.50/1.73  fof(f188,plain,(
% 10.50/1.73    ( ! [X0] : (k2_zfmisc_1(sK2,k4_xboole_0(sK3,X0)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))) )),
% 10.50/1.73    inference(superposition,[],[f61,f37])).
% 10.50/1.73  fof(f37,plain,(
% 10.50/1.73    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 10.50/1.73    inference(cnf_transformation,[],[f26])).
% 10.50/1.73  fof(f26,plain,(
% 10.50/1.73    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 10.50/1.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f25])).
% 10.50/1.73  fof(f25,plain,(
% 10.50/1.73    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 10.50/1.73    introduced(choice_axiom,[])).
% 10.50/1.73  fof(f20,plain,(
% 10.50/1.73    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 10.50/1.73    inference(flattening,[],[f19])).
% 10.50/1.73  fof(f19,plain,(
% 10.50/1.73    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 10.50/1.73    inference(ennf_transformation,[],[f17])).
% 10.50/1.73  fof(f17,negated_conjecture,(
% 10.50/1.73    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 10.50/1.73    inference(negated_conjecture,[],[f16])).
% 10.50/1.73  fof(f16,conjecture,(
% 10.50/1.73    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 10.50/1.73  fof(f61,plain,(
% 10.50/1.73    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 10.50/1.73    inference(cnf_transformation,[],[f15])).
% 10.50/1.73  fof(f15,axiom,(
% 10.50/1.73    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 10.50/1.73  fof(f6993,plain,(
% 10.50/1.73    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 10.50/1.73    inference(forward_demodulation,[],[f6960,f37])).
% 10.50/1.73  fof(f6960,plain,(
% 10.50/1.73    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1))),
% 10.50/1.73    inference(superposition,[],[f3730,f138])).
% 10.50/1.73  fof(f138,plain,(
% 10.50/1.73    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 10.50/1.73    inference(forward_demodulation,[],[f132,f42])).
% 10.50/1.73  fof(f42,plain,(
% 10.50/1.73    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 10.50/1.73    inference(cnf_transformation,[],[f9])).
% 10.50/1.73  fof(f9,axiom,(
% 10.50/1.73    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 10.50/1.73  fof(f132,plain,(
% 10.50/1.73    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 10.50/1.73    inference(superposition,[],[f46,f112])).
% 10.50/1.73  fof(f112,plain,(
% 10.50/1.73    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 10.50/1.73    inference(forward_demodulation,[],[f101,f41])).
% 10.50/1.73  fof(f41,plain,(
% 10.50/1.73    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 10.50/1.73    inference(cnf_transformation,[],[f6])).
% 10.50/1.73  fof(f6,axiom,(
% 10.50/1.73    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 10.50/1.73  fof(f101,plain,(
% 10.50/1.73    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 10.50/1.73    inference(superposition,[],[f46,f42])).
% 10.50/1.73  fof(f46,plain,(
% 10.50/1.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 10.50/1.73    inference(cnf_transformation,[],[f10])).
% 10.50/1.73  fof(f10,axiom,(
% 10.50/1.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 10.50/1.73  fof(f3730,plain,(
% 10.50/1.73    ( ! [X32] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X32,sK2),sK3),k2_zfmisc_1(X32,sK1))) )),
% 10.50/1.73    inference(superposition,[],[f111,f1624])).
% 10.50/1.73  fof(f1624,plain,(
% 10.50/1.73    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(sK0,sK3))) )),
% 10.50/1.73    inference(backward_demodulation,[],[f1213,f1607])).
% 10.50/1.73  fof(f1607,plain,(
% 10.50/1.73    ( ! [X6,X7,X5] : (k4_xboole_0(k2_zfmisc_1(X5,X6),k2_zfmisc_1(k4_xboole_0(X5,X7),X6)) = k2_zfmisc_1(k3_xboole_0(X5,X7),X6)) )),
% 10.50/1.73    inference(backward_demodulation,[],[f173,f1606])).
% 10.50/1.73  fof(f1606,plain,(
% 10.50/1.73    ( ! [X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4)) = k2_zfmisc_1(k3_xboole_0(X3,X5),X4)) )),
% 10.50/1.73    inference(forward_demodulation,[],[f1556,f46])).
% 10.50/1.73  fof(f1556,plain,(
% 10.50/1.73    ( ! [X4,X5,X3] : (k2_zfmisc_1(k4_xboole_0(X3,k4_xboole_0(X3,X5)),X4) = k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4))) )),
% 10.50/1.73    inference(superposition,[],[f173,f60])).
% 10.50/1.73  fof(f60,plain,(
% 10.50/1.73    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 10.50/1.73    inference(cnf_transformation,[],[f15])).
% 10.50/1.73  fof(f173,plain,(
% 10.50/1.73    ( ! [X6,X7,X5] : (k3_xboole_0(k2_zfmisc_1(X5,X6),k2_zfmisc_1(X7,X6)) = k4_xboole_0(k2_zfmisc_1(X5,X6),k2_zfmisc_1(k4_xboole_0(X5,X7),X6))) )),
% 10.50/1.73    inference(superposition,[],[f46,f60])).
% 10.50/1.73  fof(f1213,plain,(
% 10.50/1.73    ( ! [X1] : (k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k4_xboole_0(X1,sK2),sK3)) = k3_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(sK0,sK3))) )),
% 10.50/1.73    inference(backward_demodulation,[],[f306,f1173])).
% 10.50/1.73  fof(f1173,plain,(
% 10.50/1.73    ( ! [X10,X8,X11,X9] : (k3_xboole_0(k2_zfmisc_1(X8,X11),k2_zfmisc_1(X9,X10)) = k3_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11))) )),
% 10.50/1.73    inference(superposition,[],[f274,f64])).
% 10.50/1.73  fof(f64,plain,(
% 10.50/1.73    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 10.50/1.73    inference(cnf_transformation,[],[f14])).
% 10.50/1.73  fof(f14,axiom,(
% 10.50/1.73    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 10.50/1.73  fof(f274,plain,(
% 10.50/1.73    ( ! [X6,X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4)) = k2_zfmisc_1(k3_xboole_0(X5,X6),k3_xboole_0(X4,X3))) )),
% 10.50/1.73    inference(superposition,[],[f64,f45])).
% 10.50/1.73  fof(f45,plain,(
% 10.50/1.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 10.50/1.73    inference(cnf_transformation,[],[f1])).
% 10.50/1.73  fof(f1,axiom,(
% 10.50/1.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 10.50/1.73  fof(f306,plain,(
% 10.50/1.73    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k4_xboole_0(X1,sK2),sK3))) )),
% 10.50/1.73    inference(superposition,[],[f46,f165])).
% 10.50/1.73  fof(f165,plain,(
% 10.50/1.73    ( ! [X0] : (k2_zfmisc_1(k4_xboole_0(X0,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 10.50/1.73    inference(superposition,[],[f60,f37])).
% 10.50/1.73  fof(f111,plain,(
% 10.50/1.73    ( ! [X8,X9] : (r1_tarski(k3_xboole_0(X8,X9),X8)) )),
% 10.50/1.73    inference(superposition,[],[f44,f46])).
% 10.50/1.73  fof(f44,plain,(
% 10.50/1.73    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 10.50/1.73    inference(cnf_transformation,[],[f8])).
% 10.50/1.73  fof(f8,axiom,(
% 10.50/1.73    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 10.50/1.73  fof(f4328,plain,(
% 10.50/1.73    k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) | r1_tarski(sK0,sK2)),
% 10.50/1.73    inference(subsumption_resolution,[],[f4315,f39])).
% 10.50/1.73  fof(f39,plain,(
% 10.50/1.73    k1_xboole_0 != sK1),
% 10.50/1.73    inference(cnf_transformation,[],[f26])).
% 10.50/1.73  fof(f4315,plain,(
% 10.50/1.73    k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) | r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 10.50/1.73    inference(resolution,[],[f350,f62])).
% 10.50/1.73  fof(f62,plain,(
% 10.50/1.73    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 10.50/1.73    inference(cnf_transformation,[],[f24])).
% 10.50/1.73  fof(f24,plain,(
% 10.50/1.73    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 10.50/1.73    inference(ennf_transformation,[],[f13])).
% 10.50/1.73  fof(f13,axiom,(
% 10.50/1.73    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 10.50/1.73  fof(f350,plain,(
% 10.50/1.73    ( ! [X6] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X6)) | k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK3,X6))) )),
% 10.50/1.73    inference(superposition,[],[f55,f188])).
% 10.50/1.73  fof(f55,plain,(
% 10.50/1.73    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 10.50/1.73    inference(cnf_transformation,[],[f34])).
% 10.50/1.73  fof(f10653,plain,(
% 10.50/1.73    sK1 = sK3 | ~r1_tarski(sK0,sK2)),
% 10.50/1.73    inference(resolution,[],[f10282,f655])).
% 10.50/1.73  fof(f655,plain,(
% 10.50/1.73    ~r1_tarski(sK1,sK3) | sK1 = sK3 | ~r1_tarski(sK0,sK2)),
% 10.50/1.73    inference(resolution,[],[f620,f52])).
% 10.50/1.73  fof(f52,plain,(
% 10.50/1.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 10.50/1.73    inference(cnf_transformation,[],[f32])).
% 10.50/1.73  fof(f32,plain,(
% 10.50/1.73    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.50/1.73    inference(flattening,[],[f31])).
% 10.50/1.73  fof(f31,plain,(
% 10.50/1.73    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.50/1.73    inference(nnf_transformation,[],[f4])).
% 10.50/1.73  fof(f4,axiom,(
% 10.50/1.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 10.50/1.73  fof(f620,plain,(
% 10.50/1.73    r1_tarski(sK3,sK1) | ~r1_tarski(sK0,sK2)),
% 10.50/1.73    inference(subsumption_resolution,[],[f612,f38])).
% 10.50/1.73  fof(f38,plain,(
% 10.50/1.73    k1_xboole_0 != sK0),
% 10.50/1.73    inference(cnf_transformation,[],[f26])).
% 10.50/1.73  fof(f612,plain,(
% 10.50/1.73    ~r1_tarski(sK0,sK2) | r1_tarski(sK3,sK1) | k1_xboole_0 = sK0),
% 10.50/1.73    inference(resolution,[],[f516,f63])).
% 10.50/1.73  fof(f63,plain,(
% 10.50/1.73    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 10.50/1.73    inference(cnf_transformation,[],[f24])).
% 10.50/1.73  fof(f516,plain,(
% 10.50/1.73    ( ! [X25] : (r1_tarski(k2_zfmisc_1(X25,sK3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X25,sK2)) )),
% 10.50/1.73    inference(superposition,[],[f266,f113])).
% 10.50/1.73  fof(f113,plain,(
% 10.50/1.73    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) )),
% 10.50/1.73    inference(forward_demodulation,[],[f102,f42])).
% 10.50/1.73  fof(f102,plain,(
% 10.50/1.73    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k4_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X1,X2)) )),
% 10.50/1.73    inference(superposition,[],[f46,f56])).
% 10.50/1.73  fof(f266,plain,(
% 10.50/1.73    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X0,sK2),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 10.50/1.73    inference(superposition,[],[f252,f45])).
% 10.50/1.73  fof(f252,plain,(
% 10.50/1.73    ( ! [X2] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,X2),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 10.50/1.73    inference(superposition,[],[f228,f46])).
% 10.50/1.73  fof(f228,plain,(
% 10.50/1.73    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(sK2,X0),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 10.50/1.73    inference(superposition,[],[f44,f162])).
% 10.50/1.73  fof(f162,plain,(
% 10.50/1.73    ( ! [X0] : (k2_zfmisc_1(k4_xboole_0(sK2,X0),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))) )),
% 10.50/1.73    inference(superposition,[],[f60,f37])).
% 10.50/1.73  fof(f10282,plain,(
% 10.50/1.73    r1_tarski(sK1,sK3)),
% 10.50/1.73    inference(trivial_inequality_removal,[],[f10174])).
% 10.50/1.73  fof(f10174,plain,(
% 10.50/1.73    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3)),
% 10.50/1.73    inference(backward_demodulation,[],[f3976,f10122])).
% 10.50/1.73  fof(f10122,plain,(
% 10.50/1.73    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 10.50/1.73    inference(forward_demodulation,[],[f10121,f112])).
% 10.50/1.73  fof(f10121,plain,(
% 10.50/1.73    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 10.50/1.73    inference(forward_demodulation,[],[f10053,f224])).
% 10.50/1.73  fof(f224,plain,(
% 10.50/1.73    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 10.50/1.73    inference(superposition,[],[f162,f61])).
% 10.50/1.73  fof(f10053,plain,(
% 10.50/1.73    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 10.50/1.73    inference(superposition,[],[f162,f8718])).
% 10.50/1.73  fof(f8718,plain,(
% 10.50/1.73    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 10.50/1.73    inference(forward_demodulation,[],[f8717,f37])).
% 10.50/1.73  fof(f8717,plain,(
% 10.50/1.73    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK3)),
% 10.50/1.73    inference(forward_demodulation,[],[f8640,f8409])).
% 10.50/1.73  fof(f8409,plain,(
% 10.50/1.73    ( ! [X9] : (k2_zfmisc_1(X9,sK3) = k2_zfmisc_1(X9,k3_xboole_0(sK1,sK3))) )),
% 10.50/1.73    inference(forward_demodulation,[],[f8408,f45])).
% 10.50/1.73  fof(f8408,plain,(
% 10.50/1.73    ( ! [X9] : (k2_zfmisc_1(X9,sK3) = k2_zfmisc_1(X9,k3_xboole_0(sK3,sK1))) )),
% 10.50/1.73    inference(forward_demodulation,[],[f8407,f42])).
% 10.50/1.73  fof(f8407,plain,(
% 10.50/1.73    ( ! [X9] : (k2_zfmisc_1(X9,k3_xboole_0(sK3,sK1)) = k4_xboole_0(k2_zfmisc_1(X9,sK3),k1_xboole_0)) )),
% 10.50/1.73    inference(forward_demodulation,[],[f8370,f67])).
% 10.50/1.73  fof(f67,plain,(
% 10.50/1.73    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 10.50/1.73    inference(equality_resolution,[],[f59])).
% 10.50/1.73  fof(f59,plain,(
% 10.50/1.73    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 10.50/1.73    inference(cnf_transformation,[],[f36])).
% 10.50/1.73  fof(f36,plain,(
% 10.50/1.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 10.50/1.73    inference(flattening,[],[f35])).
% 10.50/1.73  fof(f35,plain,(
% 10.50/1.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 10.50/1.73    inference(nnf_transformation,[],[f12])).
% 10.50/1.73  fof(f12,axiom,(
% 10.50/1.73    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 10.50/1.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 10.50/1.73  fof(f8370,plain,(
% 10.50/1.73    ( ! [X9] : (k2_zfmisc_1(X9,k3_xboole_0(sK3,sK1)) = k4_xboole_0(k2_zfmisc_1(X9,sK3),k2_zfmisc_1(X9,k1_xboole_0))) )),
% 10.50/1.73    inference(superposition,[],[f1910,f7737])).
% 10.50/1.73  fof(f7737,plain,(
% 10.50/1.73    k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 10.50/1.73    inference(subsumption_resolution,[],[f7727,f38])).
% 10.50/1.73  fof(f7727,plain,(
% 10.50/1.73    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 10.50/1.73    inference(trivial_inequality_removal,[],[f7680])).
% 10.50/1.73  fof(f7680,plain,(
% 10.50/1.73    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 10.50/1.73    inference(superposition,[],[f57,f7338])).
% 10.50/1.73  fof(f7338,plain,(
% 10.50/1.73    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))),
% 10.50/1.73    inference(forward_demodulation,[],[f7250,f68])).
% 10.50/1.73  fof(f68,plain,(
% 10.50/1.73    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 10.50/1.73    inference(equality_resolution,[],[f58])).
% 10.50/1.73  fof(f58,plain,(
% 10.50/1.73    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 10.50/1.73    inference(cnf_transformation,[],[f36])).
% 10.50/1.73  fof(f7250,plain,(
% 10.50/1.73    k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))),
% 10.50/1.73    inference(backward_demodulation,[],[f301,f7249])).
% 10.50/1.73  fof(f7249,plain,(
% 10.50/1.73    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 10.50/1.73    inference(subsumption_resolution,[],[f7232,f39])).
% 10.50/1.73  fof(f7232,plain,(
% 10.50/1.73    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 10.50/1.73    inference(trivial_inequality_removal,[],[f7185])).
% 10.50/1.73  fof(f7185,plain,(
% 10.50/1.73    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 10.50/1.73    inference(superposition,[],[f57,f7032])).
% 10.50/1.73  fof(f7032,plain,(
% 10.50/1.73    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 10.50/1.73    inference(backward_demodulation,[],[f341,f7025])).
% 10.50/1.73  fof(f341,plain,(
% 10.50/1.73    k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))),
% 10.50/1.73    inference(superposition,[],[f188,f60])).
% 10.50/1.73  fof(f301,plain,(
% 10.50/1.73    k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK3)),
% 10.50/1.73    inference(superposition,[],[f165,f61])).
% 10.50/1.73  fof(f57,plain,(
% 10.50/1.73    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 10.50/1.73    inference(cnf_transformation,[],[f36])).
% 10.50/1.73  fof(f1910,plain,(
% 10.50/1.73    ( ! [X8,X7,X9] : (k4_xboole_0(k2_zfmisc_1(X7,X8),k2_zfmisc_1(X7,k4_xboole_0(X8,X9))) = k2_zfmisc_1(X7,k3_xboole_0(X8,X9))) )),
% 10.50/1.73    inference(backward_demodulation,[],[f201,f1909])).
% 10.50/1.73  fof(f1909,plain,(
% 10.50/1.73    ( ! [X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(X3,k3_xboole_0(X4,X5))) )),
% 10.50/1.73    inference(forward_demodulation,[],[f1847,f46])).
% 10.50/1.73  fof(f1847,plain,(
% 10.50/1.73    ( ! [X4,X5,X3] : (k2_zfmisc_1(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5))) )),
% 10.50/1.73    inference(superposition,[],[f201,f61])).
% 10.50/1.73  fof(f201,plain,(
% 10.50/1.73    ( ! [X8,X7,X9] : (k3_xboole_0(k2_zfmisc_1(X7,X8),k2_zfmisc_1(X7,X9)) = k4_xboole_0(k2_zfmisc_1(X7,X8),k2_zfmisc_1(X7,k4_xboole_0(X8,X9)))) )),
% 10.50/1.73    inference(superposition,[],[f46,f61])).
% 10.50/1.73  fof(f8640,plain,(
% 10.50/1.73    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 10.50/1.73    inference(superposition,[],[f8476,f138])).
% 10.50/1.73  fof(f8476,plain,(
% 10.50/1.73    ( ! [X1] : (k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X1))) )),
% 10.50/1.73    inference(backward_demodulation,[],[f1928,f8454])).
% 10.50/1.73  fof(f8454,plain,(
% 10.50/1.73    ( ! [X2,X1] : (k3_xboole_0(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK2,X2)) = k2_zfmisc_1(sK0,k3_xboole_0(X1,X2))) )),
% 10.50/1.73    inference(superposition,[],[f64,f8207])).
% 10.50/1.73  fof(f8207,plain,(
% 10.50/1.73    sK0 = k3_xboole_0(sK0,sK2)),
% 10.50/1.73    inference(forward_demodulation,[],[f8180,f42])).
% 10.50/1.73  fof(f8180,plain,(
% 10.50/1.73    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 10.50/1.73    inference(superposition,[],[f46,f7249])).
% 10.50/1.73  fof(f1928,plain,(
% 10.50/1.73    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3))) )),
% 10.50/1.73    inference(backward_demodulation,[],[f398,f1910])).
% 10.50/1.73  fof(f398,plain,(
% 10.50/1.73    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k4_xboole_0(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(sK2,k4_xboole_0(X1,sK3)))) )),
% 10.50/1.73    inference(forward_demodulation,[],[f381,f45])).
% 10.50/1.73  fof(f381,plain,(
% 10.50/1.73    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(sK2,k4_xboole_0(X1,sK3)))) )),
% 10.50/1.73    inference(superposition,[],[f46,f191])).
% 10.50/1.73  fof(f191,plain,(
% 10.50/1.73    ( ! [X0] : (k2_zfmisc_1(sK2,k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1))) )),
% 10.50/1.73    inference(superposition,[],[f61,f37])).
% 10.50/1.73  fof(f3976,plain,(
% 10.50/1.73    k1_xboole_0 != k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) | r1_tarski(sK1,sK3)),
% 10.50/1.73    inference(forward_demodulation,[],[f3975,f224])).
% 10.50/1.73  fof(f3975,plain,(
% 10.50/1.73    k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) | r1_tarski(sK1,sK3)),
% 10.50/1.73    inference(subsumption_resolution,[],[f3966,f38])).
% 10.50/1.73  fof(f3966,plain,(
% 10.50/1.73    k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) | r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 10.50/1.73    inference(resolution,[],[f234,f63])).
% 10.50/1.73  fof(f234,plain,(
% 10.50/1.73    ( ! [X6] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X6,sK3)) | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(sK2,X6),sK3)) )),
% 10.50/1.73    inference(superposition,[],[f55,f162])).
% 10.50/1.73  fof(f12389,plain,(
% 10.50/1.73    sK1 != sK3),
% 10.50/1.73    inference(trivial_inequality_removal,[],[f12214])).
% 10.50/1.73  fof(f12214,plain,(
% 10.50/1.73    sK0 != sK0 | sK1 != sK3),
% 10.50/1.73    inference(backward_demodulation,[],[f40,f12213])).
% 10.50/1.73  fof(f12213,plain,(
% 10.50/1.73    sK0 = sK2),
% 10.50/1.73    inference(subsumption_resolution,[],[f12212,f7087])).
% 10.50/1.74  fof(f12212,plain,(
% 10.50/1.74    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 10.50/1.74    inference(subsumption_resolution,[],[f10735,f65])).
% 10.50/1.74  fof(f65,plain,(
% 10.50/1.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 10.50/1.74    inference(equality_resolution,[],[f51])).
% 10.50/1.74  fof(f51,plain,(
% 10.50/1.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 10.50/1.74    inference(cnf_transformation,[],[f32])).
% 10.50/1.74  fof(f10735,plain,(
% 10.50/1.74    ~r1_tarski(sK1,sK1) | sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 10.50/1.74    inference(backward_demodulation,[],[f774,f10665])).
% 10.50/1.74  fof(f774,plain,(
% 10.50/1.74    ~r1_tarski(sK1,sK3) | sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 10.50/1.74    inference(resolution,[],[f759,f52])).
% 10.50/1.74  fof(f759,plain,(
% 10.50/1.74    r1_tarski(sK2,sK0) | ~r1_tarski(sK1,sK3)),
% 10.50/1.74    inference(subsumption_resolution,[],[f752,f39])).
% 10.50/1.74  fof(f752,plain,(
% 10.50/1.74    ~r1_tarski(sK1,sK3) | r1_tarski(sK2,sK0) | k1_xboole_0 = sK1),
% 10.50/1.74    inference(resolution,[],[f517,f62])).
% 10.50/1.74  fof(f517,plain,(
% 10.50/1.74    ( ! [X26] : (r1_tarski(k2_zfmisc_1(sK2,X26),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X26,sK3)) )),
% 10.50/1.74    inference(superposition,[],[f401,f113])).
% 10.50/1.74  fof(f401,plain,(
% 10.50/1.74    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)),k2_zfmisc_1(sK0,sK1))) )),
% 10.50/1.74    inference(superposition,[],[f367,f45])).
% 10.50/1.74  fof(f367,plain,(
% 10.50/1.74    ( ! [X2] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)),k2_zfmisc_1(sK0,sK1))) )),
% 10.50/1.74    inference(superposition,[],[f346,f46])).
% 10.50/1.74  fof(f346,plain,(
% 10.50/1.74    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1))) )),
% 10.50/1.74    inference(superposition,[],[f44,f188])).
% 10.50/1.74  fof(f40,plain,(
% 10.50/1.74    sK1 != sK3 | sK0 != sK2),
% 10.50/1.74    inference(cnf_transformation,[],[f26])).
% 10.50/1.74  % SZS output end Proof for theBenchmark
% 10.50/1.74  % (28816)------------------------------
% 10.50/1.74  % (28816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.50/1.74  % (28816)Termination reason: Refutation
% 10.50/1.74  
% 10.50/1.74  % (28816)Memory used [KB]: 8699
% 10.50/1.74  % (28816)Time elapsed: 1.249 s
% 10.50/1.74  % (28816)------------------------------
% 10.50/1.74  % (28816)------------------------------
% 10.50/1.74  % (28803)Success in time 1.386 s
%------------------------------------------------------------------------------
