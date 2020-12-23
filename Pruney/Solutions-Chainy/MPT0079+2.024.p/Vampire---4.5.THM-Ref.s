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
% DateTime   : Thu Dec  3 12:30:54 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 289 expanded)
%              Number of leaves         :   18 (  84 expanded)
%              Depth                    :   22
%              Number of atoms          :  175 ( 700 expanded)
%              Number of equality atoms :   73 ( 305 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2147,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2146,f36])).

fof(f36,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f2146,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f2125,f1467])).

fof(f1467,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f1436,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1436,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f1113,f61])).

fof(f61,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f40,f33])).

fof(f33,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1113,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_xboole_0(sK0,X0))
      | k2_xboole_0(sK2,X0) = X0 ) ),
    inference(resolution,[],[f1013,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1013,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | ~ r1_tarski(sK2,k2_xboole_0(sK0,X0)) ) ),
    inference(superposition,[],[f55,f994])).

fof(f994,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f928,f66])).

fof(f66,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f43,f37])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f928,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f57,f508])).

fof(f508,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f504,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f504,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),X0) ),
    inference(resolution,[],[f500,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f500,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f58,f34])).

fof(f34,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f49,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f47,f44])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f2125,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f429,f2098])).

fof(f2098,plain,(
    sK1 = k4_xboole_0(sK2,sK3) ),
    inference(backward_demodulation,[],[f206,f1918])).

fof(f1918,plain,(
    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(forward_demodulation,[],[f1904,f1081])).

fof(f1081,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f927,f66])).

fof(f927,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f57,f729])).

fof(f729,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f56,f512])).

fof(f512,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f506,f39])).

fof(f506,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)),X0) ),
    inference(resolution,[],[f501,f50])).

fof(f501,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) ),
    inference(resolution,[],[f58,f35])).

fof(f35,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f44,f44])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1904,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f46,f1840])).

fof(f1840,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f1835,f43])).

fof(f1835,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f1820,f94])).

fof(f94,plain,(
    ! [X4] : k2_xboole_0(X4,X4) = X4 ),
    inference(resolution,[],[f53,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f40,f37])).

fof(f1820,plain,(
    k2_xboole_0(sK3,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f1438,f648])).

fof(f648,plain,(
    ! [X35] : k2_xboole_0(sK2,k2_xboole_0(sK3,X35)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X35)) ),
    inference(forward_demodulation,[],[f597,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f597,plain,(
    ! [X35] : k2_xboole_0(sK2,k2_xboole_0(sK3,X35)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X35) ),
    inference(superposition,[],[f54,f33])).

fof(f1438,plain,(
    ! [X1] : k2_xboole_0(X1,sK1) = k2_xboole_0(sK2,k2_xboole_0(X1,sK1)) ),
    inference(resolution,[],[f1113,f1204])).

fof(f1204,plain,(
    ! [X0] : r1_tarski(sK2,k2_xboole_0(sK0,k2_xboole_0(X0,sK1))) ),
    inference(superposition,[],[f1185,f43])).

fof(f1185,plain,(
    ! [X0] : r1_tarski(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X0))) ),
    inference(superposition,[],[f40,f648])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f206,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[],[f46,f33])).

fof(f429,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f423,f62])).

fof(f423,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))
    | sK2 = k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) ),
    inference(superposition,[],[f419,f226])).

fof(f226,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f225,f93])).

fof(f93,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f53,f80])).

fof(f80,plain,(
    r1_tarski(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f70,f33])).

fof(f70,plain,(
    ! [X4,X3] : r1_tarski(X3,k2_xboole_0(X4,X3)) ),
    inference(superposition,[],[f40,f43])).

fof(f225,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f223,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f223,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f45,f206])).

fof(f419,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0))
      | k2_xboole_0(k4_xboole_0(sK2,sK3),X0) = X0 ) ),
    inference(resolution,[],[f417,f53])).

fof(f417,plain,(
    ! [X24] :
      ( r1_tarski(k4_xboole_0(sK2,sK3),X24)
      | ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X24)) ) ),
    inference(superposition,[],[f55,f206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:43:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (30105)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (30096)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (30094)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (30101)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (30122)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.52  % (30100)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (30108)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (30098)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (30119)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (30099)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (30104)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (30118)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (30110)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (30111)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (30112)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (30112)Refutation not found, incomplete strategy% (30112)------------------------------
% 0.22/0.54  % (30112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30112)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30112)Memory used [KB]: 10618
% 0.22/0.54  % (30112)Time elapsed: 0.121 s
% 0.22/0.54  % (30112)------------------------------
% 0.22/0.54  % (30112)------------------------------
% 0.22/0.54  % (30103)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (30114)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (30120)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (30095)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (30109)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (30106)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (30121)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (30113)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (30115)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (30102)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (30116)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.46/0.56  % (30123)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.56  % (30107)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.46/0.56  % (30124)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.46/0.56  % (30117)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.60/0.63  % (30098)Refutation found. Thanks to Tanya!
% 1.60/0.63  % SZS status Theorem for theBenchmark
% 1.98/0.63  % SZS output start Proof for theBenchmark
% 1.98/0.63  fof(f2147,plain,(
% 1.98/0.63    $false),
% 1.98/0.63    inference(subsumption_resolution,[],[f2146,f36])).
% 1.98/0.64  fof(f36,plain,(
% 1.98/0.64    sK1 != sK2),
% 1.98/0.64    inference(cnf_transformation,[],[f28])).
% 1.98/0.64  fof(f28,plain,(
% 1.98/0.64    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.98/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f27])).
% 1.98/0.64  fof(f27,plain,(
% 1.98/0.64    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.98/0.64    introduced(choice_axiom,[])).
% 1.98/0.64  fof(f21,plain,(
% 1.98/0.64    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.98/0.64    inference(flattening,[],[f20])).
% 1.98/0.64  fof(f20,plain,(
% 1.98/0.64    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.98/0.64    inference(ennf_transformation,[],[f17])).
% 1.98/0.64  fof(f17,negated_conjecture,(
% 1.98/0.64    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.98/0.64    inference(negated_conjecture,[],[f16])).
% 1.98/0.64  fof(f16,conjecture,(
% 1.98/0.64    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.98/0.64  fof(f2146,plain,(
% 1.98/0.64    sK1 = sK2),
% 1.98/0.64    inference(forward_demodulation,[],[f2125,f1467])).
% 1.98/0.64  fof(f1467,plain,(
% 1.98/0.64    sK1 = k2_xboole_0(sK1,sK2)),
% 1.98/0.64    inference(superposition,[],[f1436,f43])).
% 1.98/0.64  fof(f43,plain,(
% 1.98/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f1])).
% 1.98/0.64  fof(f1,axiom,(
% 1.98/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.98/0.64  fof(f1436,plain,(
% 1.98/0.64    sK1 = k2_xboole_0(sK2,sK1)),
% 1.98/0.64    inference(resolution,[],[f1113,f61])).
% 1.98/0.64  fof(f61,plain,(
% 1.98/0.64    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 1.98/0.64    inference(superposition,[],[f40,f33])).
% 1.98/0.64  fof(f33,plain,(
% 1.98/0.64    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.98/0.64    inference(cnf_transformation,[],[f28])).
% 1.98/0.64  fof(f40,plain,(
% 1.98/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.98/0.64    inference(cnf_transformation,[],[f15])).
% 1.98/0.64  fof(f15,axiom,(
% 1.98/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.98/0.64  fof(f1113,plain,(
% 1.98/0.64    ( ! [X0] : (~r1_tarski(sK2,k2_xboole_0(sK0,X0)) | k2_xboole_0(sK2,X0) = X0) )),
% 1.98/0.64    inference(resolution,[],[f1013,f53])).
% 1.98/0.64  fof(f53,plain,(
% 1.98/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.98/0.64    inference(cnf_transformation,[],[f25])).
% 1.98/0.64  fof(f25,plain,(
% 1.98/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.98/0.64    inference(ennf_transformation,[],[f5])).
% 1.98/0.64  fof(f5,axiom,(
% 1.98/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.98/0.64  fof(f1013,plain,(
% 1.98/0.64    ( ! [X0] : (r1_tarski(sK2,X0) | ~r1_tarski(sK2,k2_xboole_0(sK0,X0))) )),
% 1.98/0.64    inference(superposition,[],[f55,f994])).
% 1.98/0.64  fof(f994,plain,(
% 1.98/0.64    sK2 = k4_xboole_0(sK2,sK0)),
% 1.98/0.64    inference(superposition,[],[f928,f66])).
% 1.98/0.64  fof(f66,plain,(
% 1.98/0.64    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.98/0.64    inference(superposition,[],[f43,f37])).
% 1.98/0.64  fof(f37,plain,(
% 1.98/0.64    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.98/0.64    inference(cnf_transformation,[],[f6])).
% 1.98/0.64  fof(f6,axiom,(
% 1.98/0.64    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.98/0.64  fof(f928,plain,(
% 1.98/0.64    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 1.98/0.64    inference(superposition,[],[f57,f508])).
% 1.98/0.64  fof(f508,plain,(
% 1.98/0.64    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.98/0.64    inference(resolution,[],[f504,f39])).
% 1.98/0.64  fof(f39,plain,(
% 1.98/0.64    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.98/0.64    inference(cnf_transformation,[],[f22])).
% 1.98/0.64  fof(f22,plain,(
% 1.98/0.64    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.98/0.64    inference(ennf_transformation,[],[f14])).
% 1.98/0.64  fof(f14,axiom,(
% 1.98/0.64    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.98/0.64  fof(f504,plain,(
% 1.98/0.64    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),X0)) )),
% 1.98/0.64    inference(resolution,[],[f500,f50])).
% 1.98/0.64  fof(f50,plain,(
% 1.98/0.64    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f32])).
% 1.98/0.64  fof(f32,plain,(
% 1.98/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.98/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f31])).
% 1.98/0.64  fof(f31,plain,(
% 1.98/0.64    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.98/0.64    introduced(choice_axiom,[])).
% 1.98/0.64  fof(f24,plain,(
% 1.98/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.98/0.64    inference(ennf_transformation,[],[f19])).
% 1.98/0.64  fof(f19,plain,(
% 1.98/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.98/0.64    inference(rectify,[],[f3])).
% 1.98/0.64  fof(f3,axiom,(
% 1.98/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.98/0.64  fof(f500,plain,(
% 1.98/0.64    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) )),
% 1.98/0.64    inference(resolution,[],[f58,f34])).
% 1.98/0.64  fof(f34,plain,(
% 1.98/0.64    r1_xboole_0(sK2,sK0)),
% 1.98/0.64    inference(cnf_transformation,[],[f28])).
% 1.98/0.64  fof(f58,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.98/0.64    inference(definition_unfolding,[],[f49,f44])).
% 1.98/0.64  fof(f44,plain,(
% 1.98/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.98/0.64    inference(cnf_transformation,[],[f11])).
% 1.98/0.64  fof(f11,axiom,(
% 1.98/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.98/0.64  fof(f49,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.98/0.64    inference(cnf_transformation,[],[f30])).
% 1.98/0.64  fof(f30,plain,(
% 1.98/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.98/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f29])).
% 1.98/0.64  fof(f29,plain,(
% 1.98/0.64    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.98/0.64    introduced(choice_axiom,[])).
% 1.98/0.64  fof(f23,plain,(
% 1.98/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.98/0.64    inference(ennf_transformation,[],[f18])).
% 1.98/0.64  fof(f18,plain,(
% 1.98/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.98/0.64    inference(rectify,[],[f4])).
% 1.98/0.64  fof(f4,axiom,(
% 1.98/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.98/0.64  fof(f57,plain,(
% 1.98/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.98/0.64    inference(definition_unfolding,[],[f47,f44])).
% 1.98/0.64  fof(f47,plain,(
% 1.98/0.64    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.98/0.64    inference(cnf_transformation,[],[f13])).
% 1.98/0.64  fof(f13,axiom,(
% 1.98/0.64    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.98/0.64  fof(f55,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.98/0.64    inference(cnf_transformation,[],[f26])).
% 1.98/0.64  fof(f26,plain,(
% 1.98/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.98/0.64    inference(ennf_transformation,[],[f9])).
% 1.98/0.64  fof(f9,axiom,(
% 1.98/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.98/0.64  fof(f2125,plain,(
% 1.98/0.64    sK2 = k2_xboole_0(sK1,sK2)),
% 1.98/0.64    inference(backward_demodulation,[],[f429,f2098])).
% 1.98/0.64  fof(f2098,plain,(
% 1.98/0.64    sK1 = k4_xboole_0(sK2,sK3)),
% 1.98/0.64    inference(backward_demodulation,[],[f206,f1918])).
% 1.98/0.64  fof(f1918,plain,(
% 1.98/0.64    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.98/0.64    inference(forward_demodulation,[],[f1904,f1081])).
% 1.98/0.64  fof(f1081,plain,(
% 1.98/0.64    sK1 = k4_xboole_0(sK1,sK3)),
% 1.98/0.64    inference(superposition,[],[f927,f66])).
% 1.98/0.64  fof(f927,plain,(
% 1.98/0.64    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 1.98/0.64    inference(superposition,[],[f57,f729])).
% 1.98/0.64  fof(f729,plain,(
% 1.98/0.64    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.98/0.64    inference(superposition,[],[f56,f512])).
% 1.98/0.64  fof(f512,plain,(
% 1.98/0.64    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.98/0.64    inference(resolution,[],[f506,f39])).
% 1.98/0.64  fof(f506,plain,(
% 1.98/0.64    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)),X0)) )),
% 1.98/0.64    inference(resolution,[],[f501,f50])).
% 1.98/0.64  fof(f501,plain,(
% 1.98/0.64    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) )),
% 1.98/0.64    inference(resolution,[],[f58,f35])).
% 1.98/0.64  fof(f35,plain,(
% 1.98/0.64    r1_xboole_0(sK3,sK1)),
% 1.98/0.64    inference(cnf_transformation,[],[f28])).
% 1.98/0.64  fof(f56,plain,(
% 1.98/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.98/0.64    inference(definition_unfolding,[],[f42,f44,f44])).
% 1.98/0.64  fof(f42,plain,(
% 1.98/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f2])).
% 1.98/0.64  fof(f2,axiom,(
% 1.98/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.98/0.64  fof(f1904,plain,(
% 1.98/0.64    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3)),
% 1.98/0.64    inference(superposition,[],[f46,f1840])).
% 1.98/0.64  fof(f1840,plain,(
% 1.98/0.64    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)),
% 1.98/0.64    inference(superposition,[],[f1835,f43])).
% 1.98/0.64  fof(f1835,plain,(
% 1.98/0.64    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK1)),
% 1.98/0.64    inference(forward_demodulation,[],[f1820,f94])).
% 1.98/0.64  fof(f94,plain,(
% 1.98/0.64    ( ! [X4] : (k2_xboole_0(X4,X4) = X4) )),
% 1.98/0.64    inference(resolution,[],[f53,f62])).
% 1.98/0.64  fof(f62,plain,(
% 1.98/0.64    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.98/0.64    inference(superposition,[],[f40,f37])).
% 1.98/0.64  fof(f1820,plain,(
% 1.98/0.64    k2_xboole_0(sK3,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK1))),
% 1.98/0.64    inference(superposition,[],[f1438,f648])).
% 1.98/0.64  fof(f648,plain,(
% 1.98/0.64    ( ! [X35] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X35)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X35))) )),
% 1.98/0.64    inference(forward_demodulation,[],[f597,f54])).
% 1.98/0.64  fof(f54,plain,(
% 1.98/0.64    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.98/0.64    inference(cnf_transformation,[],[f12])).
% 1.98/0.64  fof(f12,axiom,(
% 1.98/0.64    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.98/0.64  fof(f597,plain,(
% 1.98/0.64    ( ! [X35] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X35)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X35)) )),
% 1.98/0.64    inference(superposition,[],[f54,f33])).
% 1.98/0.64  fof(f1438,plain,(
% 1.98/0.64    ( ! [X1] : (k2_xboole_0(X1,sK1) = k2_xboole_0(sK2,k2_xboole_0(X1,sK1))) )),
% 1.98/0.64    inference(resolution,[],[f1113,f1204])).
% 1.98/0.64  fof(f1204,plain,(
% 1.98/0.64    ( ! [X0] : (r1_tarski(sK2,k2_xboole_0(sK0,k2_xboole_0(X0,sK1)))) )),
% 1.98/0.64    inference(superposition,[],[f1185,f43])).
% 1.98/0.64  fof(f1185,plain,(
% 1.98/0.64    ( ! [X0] : (r1_tarski(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X0)))) )),
% 1.98/0.64    inference(superposition,[],[f40,f648])).
% 1.98/0.64  fof(f46,plain,(
% 1.98/0.64    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.98/0.64    inference(cnf_transformation,[],[f8])).
% 1.98/0.64  fof(f8,axiom,(
% 1.98/0.64    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.98/0.64  fof(f206,plain,(
% 1.98/0.64    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK2,sK3)),
% 1.98/0.64    inference(superposition,[],[f46,f33])).
% 1.98/0.64  fof(f429,plain,(
% 1.98/0.64    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK3),sK2)),
% 1.98/0.64    inference(subsumption_resolution,[],[f423,f62])).
% 1.98/0.64  fof(f423,plain,(
% 1.98/0.64    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) | sK2 = k2_xboole_0(k4_xboole_0(sK2,sK3),sK2)),
% 1.98/0.64    inference(superposition,[],[f419,f226])).
% 1.98/0.64  fof(f226,plain,(
% 1.98/0.64    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 1.98/0.64    inference(forward_demodulation,[],[f225,f93])).
% 1.98/0.64  fof(f93,plain,(
% 1.98/0.64    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.98/0.64    inference(resolution,[],[f53,f80])).
% 1.98/0.64  fof(f80,plain,(
% 1.98/0.64    r1_tarski(sK3,k2_xboole_0(sK0,sK1))),
% 1.98/0.64    inference(superposition,[],[f70,f33])).
% 1.98/0.64  fof(f70,plain,(
% 1.98/0.64    ( ! [X4,X3] : (r1_tarski(X3,k2_xboole_0(X4,X3))) )),
% 1.98/0.64    inference(superposition,[],[f40,f43])).
% 1.98/0.64  fof(f225,plain,(
% 1.98/0.64    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.98/0.64    inference(forward_demodulation,[],[f223,f45])).
% 1.98/0.64  fof(f45,plain,(
% 1.98/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.98/0.64    inference(cnf_transformation,[],[f7])).
% 1.98/0.64  fof(f7,axiom,(
% 1.98/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.98/0.64  fof(f223,plain,(
% 1.98/0.64    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 1.98/0.64    inference(superposition,[],[f45,f206])).
% 1.98/0.64  fof(f419,plain,(
% 1.98/0.64    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0)) | k2_xboole_0(k4_xboole_0(sK2,sK3),X0) = X0) )),
% 1.98/0.64    inference(resolution,[],[f417,f53])).
% 1.98/0.64  fof(f417,plain,(
% 1.98/0.64    ( ! [X24] : (r1_tarski(k4_xboole_0(sK2,sK3),X24) | ~r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X24))) )),
% 1.98/0.64    inference(superposition,[],[f55,f206])).
% 1.98/0.64  % SZS output end Proof for theBenchmark
% 1.98/0.64  % (30098)------------------------------
% 1.98/0.64  % (30098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.64  % (30098)Termination reason: Refutation
% 1.98/0.64  
% 1.98/0.64  % (30098)Memory used [KB]: 11769
% 1.98/0.64  % (30098)Time elapsed: 0.188 s
% 1.98/0.64  % (30098)------------------------------
% 1.98/0.64  % (30098)------------------------------
% 1.98/0.64  % (30093)Success in time 0.265 s
%------------------------------------------------------------------------------
