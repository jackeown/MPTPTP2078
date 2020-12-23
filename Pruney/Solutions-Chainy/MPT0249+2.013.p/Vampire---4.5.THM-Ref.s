%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:12 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 809 expanded)
%              Number of leaves         :   19 ( 212 expanded)
%              Depth                    :   26
%              Number of atoms          :  246 (2524 expanded)
%              Number of equality atoms :  112 (1060 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f903,plain,(
    $false ),
    inference(subsumption_resolution,[],[f900,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f900,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f899,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != X4
      | X3 = X4
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f66,f108])).

fof(f108,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | k1_xboole_0 != X2 ) ),
    inference(resolution,[],[f70,f103])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | k1_xboole_0 != X1 ) ),
    inference(forward_demodulation,[],[f102,f55])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f102,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != X1
      | ~ r2_hidden(X2,k3_xboole_0(X1,X1)) ) ),
    inference(resolution,[],[f100,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f100,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f68,f55])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f899,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f898,f849])).

fof(f849,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f806,f831])).

fof(f831,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f827,f49])).

fof(f49,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f827,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = sK2 ),
    inference(superposition,[],[f116,f720])).

fof(f720,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f664,f300])).

fof(f300,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f261,f261])).

fof(f261,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f256,f58])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f256,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f229,f197])).

fof(f197,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f196,f55])).

fof(f196,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f190,f54])).

fof(f54,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f190,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f61,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f229,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f79,f52])).

fof(f79,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f664,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f195,f661])).

fof(f661,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f119,f660])).

fof(f660,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f657,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f657,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f656,f134])).

fof(f656,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f70,f653])).

fof(f653,plain,(
    sK0 = sK4(sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f651,f50])).

fof(f651,plain,
    ( sK0 = sK4(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f644,f134])).

fof(f644,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | sK0 = sK4(sK1,X0) ) ),
    inference(resolution,[],[f642,f88])).

fof(f88,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f642,plain,(
    ! [X19] :
      ( r2_hidden(sK4(sK1,X19),k1_tarski(sK0))
      | r1_tarski(sK1,X19) ) ),
    inference(resolution,[],[f123,f92])).

fof(f92,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f56,f48])).

fof(f48,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f123,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X5,X7)
      | r2_hidden(sK4(X5,X6),X7)
      | r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f69,f70])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f118,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f118,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f66,f92])).

fof(f195,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f61,f48])).

fof(f116,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,k3_xboole_0(X5,X6))
      | k3_xboole_0(X5,X6) = X5 ) ),
    inference(resolution,[],[f66,f57])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f806,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(superposition,[],[f77,f661])).

fof(f898,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(superposition,[],[f70,f895])).

fof(f895,plain,(
    sK0 = sK4(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f893,f51])).

fof(f893,plain,
    ( sK0 = sK4(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f872,f134])).

fof(f872,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | sK0 = sK4(sK2,X0) ) ),
    inference(resolution,[],[f832,f808])).

fof(f808,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | sK0 = X2 ) ),
    inference(superposition,[],[f88,f661])).

fof(f832,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f830,f123])).

fof(f830,plain,(
    r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f57,f720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:07:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (26755)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (26764)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (26764)Refutation not found, incomplete strategy% (26764)------------------------------
% 0.21/0.51  % (26764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26764)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26764)Memory used [KB]: 10618
% 0.21/0.51  % (26764)Time elapsed: 0.104 s
% 0.21/0.51  % (26764)------------------------------
% 0.21/0.51  % (26764)------------------------------
% 1.25/0.52  % (26756)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.52  % (26772)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.52  % (26760)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.53  % (26770)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.53  % (26777)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.54  % (26757)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.40/0.54  % (26765)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.54  % (26769)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.54  % (26779)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.55  % (26754)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.55  % (26763)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.55  % (26781)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.55  % (26766)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.56  % (26773)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.56  % (26771)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.57  % (26776)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.40/0.57  % (26758)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.57  % (26762)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.58  % (26774)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.58  % (26768)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.58  % (26782)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.58  % (26761)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.59  % (26780)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.04/0.63  % (26783)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.04/0.63  % (26775)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.04/0.64  % (26767)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.04/0.64  % (26784)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.04/0.65  % (26759)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 2.04/0.65  % (26778)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.04/0.66  % (26761)Refutation found. Thanks to Tanya!
% 2.04/0.66  % SZS status Theorem for theBenchmark
% 2.04/0.66  % SZS output start Proof for theBenchmark
% 2.04/0.66  fof(f903,plain,(
% 2.04/0.66    $false),
% 2.04/0.66    inference(subsumption_resolution,[],[f900,f51])).
% 2.04/0.66  fof(f51,plain,(
% 2.04/0.66    k1_xboole_0 != sK2),
% 2.04/0.66    inference(cnf_transformation,[],[f33])).
% 2.04/0.66  fof(f33,plain,(
% 2.04/0.66    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.04/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32])).
% 2.04/0.66  fof(f32,plain,(
% 2.04/0.66    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.04/0.66    introduced(choice_axiom,[])).
% 2.04/0.66  fof(f29,plain,(
% 2.04/0.66    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.04/0.66    inference(ennf_transformation,[],[f25])).
% 2.04/0.66  fof(f25,negated_conjecture,(
% 2.04/0.66    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.04/0.66    inference(negated_conjecture,[],[f24])).
% 2.04/0.66  fof(f24,conjecture,(
% 2.04/0.66    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 2.04/0.66  fof(f900,plain,(
% 2.04/0.66    k1_xboole_0 = sK2),
% 2.04/0.66    inference(resolution,[],[f899,f134])).
% 2.04/0.66  fof(f134,plain,(
% 2.04/0.66    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.04/0.66    inference(equality_resolution,[],[f115])).
% 2.04/0.66  fof(f115,plain,(
% 2.04/0.66    ( ! [X4,X3] : (k1_xboole_0 != X4 | X3 = X4 | ~r1_tarski(X3,X4)) )),
% 2.04/0.66    inference(resolution,[],[f66,f108])).
% 2.04/0.66  fof(f108,plain,(
% 2.04/0.66    ( ! [X2,X3] : (r1_tarski(X2,X3) | k1_xboole_0 != X2) )),
% 2.04/0.66    inference(resolution,[],[f70,f103])).
% 2.04/0.66  fof(f103,plain,(
% 2.04/0.66    ( ! [X2,X1] : (~r2_hidden(X2,X1) | k1_xboole_0 != X1) )),
% 2.04/0.66    inference(forward_demodulation,[],[f102,f55])).
% 2.04/0.66  fof(f55,plain,(
% 2.04/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.04/0.66    inference(cnf_transformation,[],[f27])).
% 2.04/0.66  fof(f27,plain,(
% 2.04/0.66    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.04/0.66    inference(rectify,[],[f6])).
% 2.04/0.66  fof(f6,axiom,(
% 2.04/0.66    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.04/0.66  fof(f102,plain,(
% 2.04/0.66    ( ! [X2,X1] : (k1_xboole_0 != X1 | ~r2_hidden(X2,k3_xboole_0(X1,X1))) )),
% 2.04/0.66    inference(resolution,[],[f100,f63])).
% 2.04/0.66  fof(f63,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f35])).
% 2.04/0.66  fof(f35,plain,(
% 2.04/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.04/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f34])).
% 2.04/0.66  fof(f34,plain,(
% 2.04/0.66    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.04/0.66    introduced(choice_axiom,[])).
% 2.04/0.66  fof(f30,plain,(
% 2.04/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.04/0.66    inference(ennf_transformation,[],[f28])).
% 2.04/0.66  fof(f28,plain,(
% 2.04/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.04/0.66    inference(rectify,[],[f7])).
% 2.04/0.66  fof(f7,axiom,(
% 2.04/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.04/0.66  fof(f100,plain,(
% 2.04/0.66    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 2.04/0.66    inference(superposition,[],[f68,f55])).
% 2.04/0.66  fof(f68,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f38])).
% 2.04/0.66  fof(f38,plain,(
% 2.04/0.66    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.04/0.66    inference(nnf_transformation,[],[f4])).
% 2.04/0.66  fof(f4,axiom,(
% 2.04/0.66    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.04/0.66  fof(f70,plain,(
% 2.04/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f42])).
% 2.04/0.66  fof(f42,plain,(
% 2.04/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 2.04/0.66  fof(f41,plain,(
% 2.04/0.66    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.04/0.66    introduced(choice_axiom,[])).
% 2.04/0.66  fof(f40,plain,(
% 2.04/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.66    inference(rectify,[],[f39])).
% 2.04/0.66  fof(f39,plain,(
% 2.04/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/0.66    inference(nnf_transformation,[],[f31])).
% 2.04/0.66  fof(f31,plain,(
% 2.04/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.04/0.66    inference(ennf_transformation,[],[f3])).
% 2.04/0.66  fof(f3,axiom,(
% 2.04/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.04/0.66  fof(f66,plain,(
% 2.04/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.04/0.66    inference(cnf_transformation,[],[f37])).
% 2.04/0.66  fof(f37,plain,(
% 2.04/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.66    inference(flattening,[],[f36])).
% 2.04/0.66  fof(f36,plain,(
% 2.04/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.66    inference(nnf_transformation,[],[f8])).
% 2.04/0.66  fof(f8,axiom,(
% 2.04/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.04/0.66  fof(f899,plain,(
% 2.04/0.66    r1_tarski(sK2,k1_xboole_0)),
% 2.04/0.66    inference(subsumption_resolution,[],[f898,f849])).
% 2.04/0.66  fof(f849,plain,(
% 2.04/0.66    ~r2_hidden(sK0,sK2)),
% 2.04/0.66    inference(resolution,[],[f806,f831])).
% 2.04/0.66  fof(f831,plain,(
% 2.04/0.66    ~r1_tarski(sK1,sK2)),
% 2.04/0.66    inference(subsumption_resolution,[],[f827,f49])).
% 2.04/0.66  fof(f49,plain,(
% 2.04/0.66    sK1 != sK2),
% 2.04/0.66    inference(cnf_transformation,[],[f33])).
% 2.04/0.66  fof(f827,plain,(
% 2.04/0.66    ~r1_tarski(sK1,sK2) | sK1 = sK2),
% 2.04/0.66    inference(superposition,[],[f116,f720])).
% 2.04/0.66  fof(f720,plain,(
% 2.04/0.66    sK2 = k3_xboole_0(sK1,sK2)),
% 2.04/0.66    inference(forward_demodulation,[],[f664,f300])).
% 2.04/0.66  fof(f300,plain,(
% 2.04/0.66    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 2.04/0.66    inference(superposition,[],[f261,f261])).
% 2.04/0.66  fof(f261,plain,(
% 2.04/0.66    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.04/0.66    inference(superposition,[],[f256,f58])).
% 2.04/0.66  fof(f58,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f1])).
% 2.04/0.66  fof(f1,axiom,(
% 2.04/0.66    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.04/0.66  fof(f256,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.04/0.66    inference(forward_demodulation,[],[f229,f197])).
% 2.04/0.66  fof(f197,plain,(
% 2.04/0.66    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.04/0.66    inference(forward_demodulation,[],[f196,f55])).
% 2.04/0.66  fof(f196,plain,(
% 2.04/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.04/0.66    inference(forward_demodulation,[],[f190,f54])).
% 2.04/0.66  fof(f54,plain,(
% 2.04/0.66    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.04/0.66    inference(cnf_transformation,[],[f26])).
% 2.04/0.66  fof(f26,plain,(
% 2.04/0.66    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.04/0.66    inference(rectify,[],[f5])).
% 2.04/0.66  fof(f5,axiom,(
% 2.04/0.66    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.04/0.66  fof(f190,plain,(
% 2.04/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 2.04/0.66    inference(superposition,[],[f61,f52])).
% 2.04/0.66  fof(f52,plain,(
% 2.04/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f12])).
% 2.04/0.66  fof(f12,axiom,(
% 2.04/0.66    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.04/0.66  fof(f61,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f13])).
% 2.04/0.66  fof(f13,axiom,(
% 2.04/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.04/0.66  fof(f229,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.04/0.66    inference(superposition,[],[f79,f52])).
% 2.04/0.66  fof(f79,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f11])).
% 2.04/0.66  fof(f11,axiom,(
% 2.04/0.66    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.04/0.66  fof(f664,plain,(
% 2.04/0.66    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 2.04/0.66    inference(backward_demodulation,[],[f195,f661])).
% 2.04/0.66  fof(f661,plain,(
% 2.04/0.66    sK1 = k1_tarski(sK0)),
% 2.04/0.66    inference(subsumption_resolution,[],[f119,f660])).
% 2.04/0.66  fof(f660,plain,(
% 2.04/0.66    r2_hidden(sK0,sK1)),
% 2.04/0.66    inference(subsumption_resolution,[],[f657,f50])).
% 2.04/0.66  fof(f50,plain,(
% 2.04/0.66    k1_xboole_0 != sK1),
% 2.04/0.66    inference(cnf_transformation,[],[f33])).
% 2.04/0.66  fof(f657,plain,(
% 2.04/0.66    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1),
% 2.04/0.66    inference(resolution,[],[f656,f134])).
% 2.04/0.66  fof(f656,plain,(
% 2.04/0.66    r1_tarski(sK1,k1_xboole_0) | r2_hidden(sK0,sK1)),
% 2.04/0.66    inference(superposition,[],[f70,f653])).
% 2.04/0.66  fof(f653,plain,(
% 2.04/0.66    sK0 = sK4(sK1,k1_xboole_0)),
% 2.04/0.66    inference(subsumption_resolution,[],[f651,f50])).
% 2.04/0.66  fof(f651,plain,(
% 2.04/0.66    sK0 = sK4(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 2.04/0.66    inference(resolution,[],[f644,f134])).
% 2.04/0.66  fof(f644,plain,(
% 2.04/0.66    ( ! [X0] : (r1_tarski(sK1,X0) | sK0 = sK4(sK1,X0)) )),
% 2.04/0.66    inference(resolution,[],[f642,f88])).
% 2.04/0.66  fof(f88,plain,(
% 2.04/0.66    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 2.04/0.66    inference(equality_resolution,[],[f72])).
% 2.04/0.66  fof(f72,plain,(
% 2.04/0.66    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.04/0.66    inference(cnf_transformation,[],[f46])).
% 2.04/0.66  fof(f46,plain,(
% 2.04/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.04/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 2.04/0.66  fof(f45,plain,(
% 2.04/0.66    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 2.04/0.66    introduced(choice_axiom,[])).
% 2.04/0.66  fof(f44,plain,(
% 2.04/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.04/0.66    inference(rectify,[],[f43])).
% 2.04/0.66  fof(f43,plain,(
% 2.04/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.04/0.66    inference(nnf_transformation,[],[f14])).
% 2.04/0.66  fof(f14,axiom,(
% 2.04/0.66    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.04/0.66  fof(f642,plain,(
% 2.04/0.66    ( ! [X19] : (r2_hidden(sK4(sK1,X19),k1_tarski(sK0)) | r1_tarski(sK1,X19)) )),
% 2.04/0.66    inference(resolution,[],[f123,f92])).
% 2.04/0.66  fof(f92,plain,(
% 2.04/0.66    r1_tarski(sK1,k1_tarski(sK0))),
% 2.04/0.66    inference(superposition,[],[f56,f48])).
% 2.04/0.66  fof(f48,plain,(
% 2.04/0.66    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.04/0.66    inference(cnf_transformation,[],[f33])).
% 2.04/0.66  fof(f56,plain,(
% 2.04/0.66    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f10])).
% 2.04/0.66  fof(f10,axiom,(
% 2.04/0.66    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.04/0.66  fof(f123,plain,(
% 2.04/0.66    ( ! [X6,X7,X5] : (~r1_tarski(X5,X7) | r2_hidden(sK4(X5,X6),X7) | r1_tarski(X5,X6)) )),
% 2.04/0.66    inference(resolution,[],[f69,f70])).
% 2.04/0.66  fof(f69,plain,(
% 2.04/0.66    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f42])).
% 2.04/0.66  fof(f119,plain,(
% 2.04/0.66    ~r2_hidden(sK0,sK1) | sK1 = k1_tarski(sK0)),
% 2.04/0.66    inference(resolution,[],[f118,f77])).
% 2.04/0.66  fof(f77,plain,(
% 2.04/0.66    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f47])).
% 2.04/0.66  fof(f47,plain,(
% 2.04/0.66    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.04/0.66    inference(nnf_transformation,[],[f22])).
% 2.04/0.66  fof(f22,axiom,(
% 2.04/0.66    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.04/0.66  fof(f118,plain,(
% 2.04/0.66    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 2.04/0.66    inference(resolution,[],[f66,f92])).
% 2.04/0.66  fof(f195,plain,(
% 2.04/0.66    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 2.04/0.66    inference(superposition,[],[f61,f48])).
% 2.04/0.66  fof(f116,plain,(
% 2.04/0.66    ( ! [X6,X5] : (~r1_tarski(X5,k3_xboole_0(X5,X6)) | k3_xboole_0(X5,X6) = X5) )),
% 2.04/0.66    inference(resolution,[],[f66,f57])).
% 2.04/0.66  fof(f57,plain,(
% 2.04/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f9])).
% 2.04/0.66  fof(f9,axiom,(
% 2.04/0.66    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.04/0.66  fof(f806,plain,(
% 2.04/0.66    ( ! [X1] : (r1_tarski(sK1,X1) | ~r2_hidden(sK0,X1)) )),
% 2.04/0.66    inference(superposition,[],[f77,f661])).
% 2.04/0.66  fof(f898,plain,(
% 2.04/0.66    r2_hidden(sK0,sK2) | r1_tarski(sK2,k1_xboole_0)),
% 2.04/0.66    inference(superposition,[],[f70,f895])).
% 2.04/0.66  fof(f895,plain,(
% 2.04/0.66    sK0 = sK4(sK2,k1_xboole_0)),
% 2.04/0.66    inference(subsumption_resolution,[],[f893,f51])).
% 2.04/0.66  fof(f893,plain,(
% 2.04/0.66    sK0 = sK4(sK2,k1_xboole_0) | k1_xboole_0 = sK2),
% 2.04/0.66    inference(resolution,[],[f872,f134])).
% 2.04/0.66  fof(f872,plain,(
% 2.04/0.66    ( ! [X0] : (r1_tarski(sK2,X0) | sK0 = sK4(sK2,X0)) )),
% 2.04/0.66    inference(resolution,[],[f832,f808])).
% 2.04/0.66  fof(f808,plain,(
% 2.04/0.66    ( ! [X2] : (~r2_hidden(X2,sK1) | sK0 = X2) )),
% 2.04/0.66    inference(superposition,[],[f88,f661])).
% 2.04/0.66  fof(f832,plain,(
% 2.04/0.66    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK1) | r1_tarski(sK2,X0)) )),
% 2.04/0.66    inference(resolution,[],[f830,f123])).
% 2.04/0.66  fof(f830,plain,(
% 2.04/0.66    r1_tarski(sK2,sK1)),
% 2.04/0.66    inference(superposition,[],[f57,f720])).
% 2.04/0.66  % SZS output end Proof for theBenchmark
% 2.04/0.66  % (26761)------------------------------
% 2.04/0.66  % (26761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.66  % (26761)Termination reason: Refutation
% 2.04/0.66  
% 2.04/0.66  % (26761)Memory used [KB]: 6908
% 2.04/0.66  % (26761)Time elapsed: 0.260 s
% 2.04/0.66  % (26761)------------------------------
% 2.04/0.66  % (26761)------------------------------
% 2.04/0.66  % (26753)Success in time 0.304 s
%------------------------------------------------------------------------------
