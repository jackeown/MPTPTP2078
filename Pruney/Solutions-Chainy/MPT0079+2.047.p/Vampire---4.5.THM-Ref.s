%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:58 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  125 (1250 expanded)
%              Number of leaves         :   16 ( 380 expanded)
%              Depth                    :   37
%              Number of atoms          :  171 (2698 expanded)
%              Number of equality atoms :  114 (1320 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2159,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2158,f30])).

fof(f30,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f21])).

fof(f21,plain,
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

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

% (30097)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f2158,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f2146,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

% (30105)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f2146,plain,(
    sK2 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1365,f2088])).

fof(f2088,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f2086,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f2086,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f2082,f1584])).

fof(f1584,plain,(
    sK2 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f1573,f1295])).

fof(f1295,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(backward_demodulation,[],[f48,f1285])).

fof(f1285,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f1280,f31])).

fof(f1280,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f985,f1266])).

fof(f1266,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f1172,f344])).

fof(f344,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f276,f331])).

fof(f331,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f320,f102])).

fof(f102,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f99,f32])).

fof(f99,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) ),
    inference(resolution,[],[f46,f29])).

fof(f29,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f320,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(superposition,[],[f204,f111])).

fof(f111,plain,(
    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
    inference(forward_demodulation,[],[f110,f63])).

fof(f63,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f55,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f55,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f52,f31])).

fof(f52,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f37,f31])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f110,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    inference(forward_demodulation,[],[f109,f33])).

fof(f109,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
    inference(superposition,[],[f36,f102])).

% (30092)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

% (30098)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f204,plain,(
    ! [X23] : k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X23)) = k4_xboole_0(k1_xboole_0,X23) ),
    inference(superposition,[],[f42,f102])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f276,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f80,f255])).

fof(f255,plain,(
    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(superposition,[],[f254,f27])).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f254,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f42,f241])).

fof(f241,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f230,f101])).

fof(f101,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f98,f32])).

fof(f98,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f46,f28])).

fof(f28,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f230,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f201,f106])).

fof(f106,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(forward_demodulation,[],[f105,f63])).

fof(f105,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(forward_demodulation,[],[f104,f33])).

fof(f104,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[],[f36,f101])).

fof(f201,plain,(
    ! [X20] : k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X20)) = k4_xboole_0(k1_xboole_0,X20) ),
    inference(superposition,[],[f42,f101])).

fof(f80,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f62,f70])).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f37,f63])).

fof(f62,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f37,f61])).

fof(f61,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f60,f27])).

fof(f60,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f59,f33])).

fof(f59,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f58,f36])).

fof(f58,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f36,f48])).

fof(f1172,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f872,f33])).

fof(f872,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f42,f825])).

fof(f825,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f799,f31])).

fof(f799,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f44,f102])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f985,plain,(
    ! [X3] : k4_xboole_0(sK2,k4_xboole_0(X3,sK0)) = k4_xboole_0(sK2,X3) ),
    inference(forward_demodulation,[],[f970,f861])).

fof(f861,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f42,f824])).

fof(f824,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f798,f31])).

fof(f798,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f44,f101])).

fof(f970,plain,(
    ! [X3] : k4_xboole_0(sK2,k4_xboole_0(X3,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X3)) ),
    inference(superposition,[],[f861,f36])).

fof(f48,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f37,f27])).

fof(f1573,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f49,f1511])).

fof(f1511,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f1503,f94])).

fof(f94,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f83,f36])).

fof(f83,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f81,f55])).

fof(f81,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f36,f70])).

fof(f1503,plain,(
    k2_xboole_0(sK3,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f487,f1485])).

fof(f1485,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f1413,f36])).

fof(f1413,plain,(
    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f1364,f33])).

fof(f1364,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(superposition,[],[f45,f1354])).

fof(f1354,plain,(
    sK2 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1353,f824])).

fof(f1353,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1343,f49])).

fof(f1343,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f37,f1310])).

% (30079)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f1310,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f1305,f57])).

fof(f57,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
    inference(forward_demodulation,[],[f54,f36])).

fof(f54,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f36,f37])).

fof(f1305,plain,(
    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f513,f1289])).

fof(f1289,plain,(
    sK0 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1288,f63])).

fof(f1288,plain,(
    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1284,f33])).

fof(f1284,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f36,f1266])).

fof(f513,plain,(
    ! [X0] : k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f484,f33])).

fof(f484,plain,(
    ! [X29] : k2_xboole_0(sK2,k2_xboole_0(sK3,X29)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X29)) ),
    inference(forward_demodulation,[],[f448,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f448,plain,(
    ! [X29] : k2_xboole_0(sK2,k2_xboole_0(sK3,X29)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X29) ),
    inference(superposition,[],[f43,f27])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f487,plain,(
    ! [X34] : k2_xboole_0(sK3,k2_xboole_0(sK2,X34)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X34)) ),
    inference(forward_demodulation,[],[f453,f43])).

fof(f453,plain,(
    ! [X34] : k2_xboole_0(sK3,k2_xboole_0(sK2,X34)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X34) ),
    inference(superposition,[],[f43,f184])).

fof(f184,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f170,f61])).

fof(f170,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f57,f27])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f37,f33])).

fof(f2082,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(resolution,[],[f100,f29])).

fof(f100,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_xboole_0(X4,X3)
      | ~ r2_hidden(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4))) ) ),
    inference(resolution,[],[f46,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1365,plain,(
    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f44,f1354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:54:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.47  % (30106)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.47  % (30082)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.51  % (30085)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.52  % (30087)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.52  % (30101)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.52  % (30099)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.52  % (30082)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.53  % (30080)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.53  % (30103)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.53  % (30093)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f2159,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(subsumption_resolution,[],[f2158,f30])).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    sK1 != sK2),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 0.23/0.53    inference(flattening,[],[f16])).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 0.23/0.53    inference(ennf_transformation,[],[f14])).
% 0.23/0.53  % (30097)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.53  fof(f14,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.23/0.53    inference(negated_conjecture,[],[f13])).
% 0.23/0.53  fof(f13,conjecture,(
% 0.23/0.53    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 0.23/0.53  fof(f2158,plain,(
% 0.23/0.53    sK1 = sK2),
% 0.23/0.53    inference(forward_demodulation,[],[f2146,f31])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,axiom,(
% 0.23/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.23/0.53  % (30105)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.53  fof(f2146,plain,(
% 0.23/0.53    sK2 = k4_xboole_0(sK1,k1_xboole_0)),
% 0.23/0.53    inference(backward_demodulation,[],[f1365,f2088])).
% 0.23/0.53  fof(f2088,plain,(
% 0.23/0.53    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.23/0.53    inference(resolution,[],[f2086,f32])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f24])).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f23])).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.23/0.53    inference(ennf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.23/0.53  fof(f2086,plain,(
% 0.23/0.53    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK1,sK2))) )),
% 0.23/0.53    inference(forward_demodulation,[],[f2082,f1584])).
% 0.23/0.53  fof(f1584,plain,(
% 0.23/0.53    sK2 = k4_xboole_0(sK1,sK3)),
% 0.23/0.53    inference(forward_demodulation,[],[f1573,f1295])).
% 0.23/0.53  fof(f1295,plain,(
% 0.23/0.53    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 0.23/0.53    inference(backward_demodulation,[],[f48,f1285])).
% 0.23/0.53  fof(f1285,plain,(
% 0.23/0.53    sK2 = k4_xboole_0(sK2,sK3)),
% 0.23/0.53    inference(forward_demodulation,[],[f1280,f31])).
% 0.23/0.53  fof(f1280,plain,(
% 0.23/0.53    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k1_xboole_0)),
% 0.23/0.53    inference(superposition,[],[f985,f1266])).
% 0.23/0.53  fof(f1266,plain,(
% 0.23/0.53    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 0.23/0.53    inference(superposition,[],[f1172,f344])).
% 0.23/0.53  fof(f344,plain,(
% 0.23/0.53    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.23/0.53    inference(backward_demodulation,[],[f276,f331])).
% 0.23/0.53  fof(f331,plain,(
% 0.23/0.53    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3)),
% 0.23/0.53    inference(forward_demodulation,[],[f320,f102])).
% 0.23/0.53  fof(f102,plain,(
% 0.23/0.53    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 0.23/0.53    inference(resolution,[],[f99,f32])).
% 0.23/0.53  fof(f99,plain,(
% 0.23/0.53    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) )),
% 0.23/0.53    inference(resolution,[],[f46,f29])).
% 0.23/0.53  fof(f29,plain,(
% 0.23/0.53    r1_xboole_0(sK3,sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f46,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.23/0.53    inference(definition_unfolding,[],[f40,f34])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,axiom,(
% 0.23/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f26])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.23/0.53    inference(ennf_transformation,[],[f15])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.53    inference(rectify,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.23/0.53  fof(f320,plain,(
% 0.23/0.53    k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(k1_xboole_0,sK3)),
% 0.23/0.53    inference(superposition,[],[f204,f111])).
% 0.23/0.53  fof(f111,plain,(
% 0.23/0.53    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3)),
% 0.23/0.53    inference(forward_demodulation,[],[f110,f63])).
% 0.23/0.53  fof(f63,plain,(
% 0.23/0.53    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.23/0.53    inference(superposition,[],[f55,f33])).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.23/0.53  fof(f55,plain,(
% 0.23/0.53    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.23/0.53    inference(forward_demodulation,[],[f52,f31])).
% 0.23/0.53  fof(f52,plain,(
% 0.23/0.53    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.23/0.53    inference(superposition,[],[f37,f31])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f7])).
% 0.23/0.53  fof(f7,axiom,(
% 0.23/0.53    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.23/0.53  fof(f110,plain,(
% 0.23/0.53    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 0.23/0.53    inference(forward_demodulation,[],[f109,f33])).
% 0.23/0.53  fof(f109,plain,(
% 0.23/0.53    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0)),
% 0.23/0.53    inference(superposition,[],[f36,f102])).
% 0.23/0.53  % (30092)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f5])).
% 0.23/0.53  fof(f5,axiom,(
% 0.23/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.23/0.53  % (30098)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.53  fof(f204,plain,(
% 0.23/0.53    ( ! [X23] : (k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X23)) = k4_xboole_0(k1_xboole_0,X23)) )),
% 0.23/0.53    inference(superposition,[],[f42,f102])).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.23/0.53  fof(f276,plain,(
% 0.23/0.53    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK3)),
% 0.23/0.53    inference(backward_demodulation,[],[f80,f255])).
% 0.23/0.53  fof(f255,plain,(
% 0.23/0.53    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK3)),
% 0.23/0.53    inference(superposition,[],[f254,f27])).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f254,plain,(
% 0.23/0.53    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X0))) )),
% 0.23/0.53    inference(superposition,[],[f42,f241])).
% 0.23/0.53  fof(f241,plain,(
% 0.23/0.53    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 0.23/0.53    inference(forward_demodulation,[],[f230,f101])).
% 0.23/0.53  fof(f101,plain,(
% 0.23/0.53    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 0.23/0.53    inference(resolution,[],[f98,f32])).
% 0.23/0.53  fof(f98,plain,(
% 0.23/0.53    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) )),
% 0.23/0.53    inference(resolution,[],[f46,f28])).
% 0.23/0.53  fof(f28,plain,(
% 0.23/0.53    r1_xboole_0(sK2,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f230,plain,(
% 0.23/0.53    k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(k1_xboole_0,sK2)),
% 0.23/0.53    inference(superposition,[],[f201,f106])).
% 0.23/0.53  fof(f106,plain,(
% 0.23/0.53    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 0.23/0.53    inference(forward_demodulation,[],[f105,f63])).
% 0.23/0.53  fof(f105,plain,(
% 0.23/0.53    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 0.23/0.53    inference(forward_demodulation,[],[f104,f33])).
% 0.23/0.53  fof(f104,plain,(
% 0.23/0.53    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0)),
% 0.23/0.53    inference(superposition,[],[f36,f101])).
% 0.23/0.53  fof(f201,plain,(
% 0.23/0.53    ( ! [X20] : (k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X20)) = k4_xboole_0(k1_xboole_0,X20)) )),
% 0.23/0.53    inference(superposition,[],[f42,f101])).
% 0.23/0.53  fof(f80,plain,(
% 0.23/0.53    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))),
% 0.23/0.53    inference(backward_demodulation,[],[f62,f70])).
% 0.23/0.53  fof(f70,plain,(
% 0.23/0.53    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 0.23/0.53    inference(superposition,[],[f37,f63])).
% 0.23/0.53  fof(f62,plain,(
% 0.23/0.53    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.23/0.53    inference(superposition,[],[f37,f61])).
% 0.23/0.53  fof(f61,plain,(
% 0.23/0.53    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.23/0.53    inference(forward_demodulation,[],[f60,f27])).
% 0.23/0.53  fof(f60,plain,(
% 0.23/0.53    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.23/0.53    inference(forward_demodulation,[],[f59,f33])).
% 0.23/0.53  fof(f59,plain,(
% 0.23/0.53    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.23/0.53    inference(forward_demodulation,[],[f58,f36])).
% 0.23/0.53  fof(f58,plain,(
% 0.23/0.53    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 0.23/0.53    inference(superposition,[],[f36,f48])).
% 0.23/0.53  fof(f1172,plain,(
% 0.23/0.53    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1))) )),
% 0.23/0.53    inference(superposition,[],[f872,f33])).
% 0.23/0.53  fof(f872,plain,(
% 0.23/0.53    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 0.23/0.53    inference(superposition,[],[f42,f825])).
% 0.23/0.53  fof(f825,plain,(
% 0.23/0.53    sK3 = k4_xboole_0(sK3,sK1)),
% 0.23/0.53    inference(forward_demodulation,[],[f799,f31])).
% 0.23/0.53  fof(f799,plain,(
% 0.23/0.53    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 0.23/0.53    inference(superposition,[],[f44,f102])).
% 0.23/0.53  fof(f44,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.23/0.53    inference(definition_unfolding,[],[f35,f34])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f9])).
% 0.23/0.53  fof(f9,axiom,(
% 0.23/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.23/0.53  fof(f985,plain,(
% 0.23/0.53    ( ! [X3] : (k4_xboole_0(sK2,k4_xboole_0(X3,sK0)) = k4_xboole_0(sK2,X3)) )),
% 0.23/0.53    inference(forward_demodulation,[],[f970,f861])).
% 0.23/0.53  fof(f861,plain,(
% 0.23/0.53    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 0.23/0.53    inference(superposition,[],[f42,f824])).
% 0.23/0.53  fof(f824,plain,(
% 0.23/0.53    sK2 = k4_xboole_0(sK2,sK0)),
% 0.23/0.53    inference(forward_demodulation,[],[f798,f31])).
% 0.23/0.53  fof(f798,plain,(
% 0.23/0.53    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 0.23/0.53    inference(superposition,[],[f44,f101])).
% 0.23/0.53  fof(f970,plain,(
% 0.23/0.53    ( ! [X3] : (k4_xboole_0(sK2,k4_xboole_0(X3,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X3))) )),
% 0.23/0.53    inference(superposition,[],[f861,f36])).
% 0.23/0.53  fof(f48,plain,(
% 0.23/0.53    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 0.23/0.53    inference(superposition,[],[f37,f27])).
% 0.23/0.53  fof(f1573,plain,(
% 0.23/0.53    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3)),
% 0.23/0.53    inference(superposition,[],[f49,f1511])).
% 0.23/0.53  fof(f1511,plain,(
% 0.23/0.53    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK1)),
% 0.23/0.53    inference(forward_demodulation,[],[f1503,f94])).
% 0.23/0.53  fof(f94,plain,(
% 0.23/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.23/0.53    inference(superposition,[],[f83,f36])).
% 0.23/0.53  fof(f83,plain,(
% 0.23/0.53    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.23/0.53    inference(forward_demodulation,[],[f81,f55])).
% 0.23/0.53  fof(f81,plain,(
% 0.23/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 0.23/0.53    inference(superposition,[],[f36,f70])).
% 0.23/0.53  fof(f1503,plain,(
% 0.23/0.53    k2_xboole_0(sK3,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK1))),
% 0.23/0.53    inference(superposition,[],[f487,f1485])).
% 0.23/0.53  fof(f1485,plain,(
% 0.23/0.53    sK1 = k2_xboole_0(sK2,sK1)),
% 0.23/0.53    inference(superposition,[],[f1413,f36])).
% 0.23/0.53  fof(f1413,plain,(
% 0.23/0.53    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 0.23/0.53    inference(superposition,[],[f1364,f33])).
% 0.23/0.53  fof(f1364,plain,(
% 0.23/0.53    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2)),
% 0.23/0.53    inference(superposition,[],[f45,f1354])).
% 0.23/0.53  fof(f1354,plain,(
% 0.23/0.53    sK2 = k4_xboole_0(sK1,sK0)),
% 0.23/0.53    inference(forward_demodulation,[],[f1353,f824])).
% 0.23/0.53  fof(f1353,plain,(
% 0.23/0.53    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0)),
% 0.23/0.53    inference(forward_demodulation,[],[f1343,f49])).
% 0.23/0.53  fof(f1343,plain,(
% 0.23/0.53    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)),
% 0.23/0.53    inference(superposition,[],[f37,f1310])).
% 0.23/0.53  % (30079)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.53  fof(f1310,plain,(
% 0.23/0.53    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0)),
% 0.23/0.53    inference(forward_demodulation,[],[f1305,f57])).
% 0.23/0.53  fof(f57,plain,(
% 0.23/0.53    ( ! [X2,X1] : (k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,X1)) )),
% 0.23/0.53    inference(forward_demodulation,[],[f54,f36])).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    ( ! [X2,X1] : (k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 0.23/0.53    inference(superposition,[],[f36,f37])).
% 0.23/0.53  fof(f1305,plain,(
% 0.23/0.53    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 0.23/0.53    inference(superposition,[],[f513,f1289])).
% 0.23/0.53  fof(f1289,plain,(
% 0.23/0.53    sK0 = k2_xboole_0(sK0,sK3)),
% 0.23/0.53    inference(forward_demodulation,[],[f1288,f63])).
% 0.23/0.53  fof(f1288,plain,(
% 0.23/0.53    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(sK0,sK3)),
% 0.23/0.53    inference(forward_demodulation,[],[f1284,f33])).
% 0.23/0.53  fof(f1284,plain,(
% 0.23/0.53    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 0.23/0.53    inference(superposition,[],[f36,f1266])).
% 0.23/0.53  fof(f513,plain,(
% 0.23/0.53    ( ! [X0] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3))) )),
% 0.23/0.53    inference(superposition,[],[f484,f33])).
% 0.23/0.53  fof(f484,plain,(
% 0.23/0.53    ( ! [X29] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X29)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X29))) )),
% 0.23/0.53    inference(forward_demodulation,[],[f448,f43])).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f11,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.23/0.53  fof(f448,plain,(
% 0.23/0.53    ( ! [X29] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X29)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X29)) )),
% 0.23/0.53    inference(superposition,[],[f43,f27])).
% 0.23/0.53  fof(f45,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.23/0.53    inference(definition_unfolding,[],[f38,f34])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,axiom,(
% 0.23/0.53    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.23/0.53  fof(f487,plain,(
% 0.23/0.53    ( ! [X34] : (k2_xboole_0(sK3,k2_xboole_0(sK2,X34)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X34))) )),
% 0.23/0.53    inference(forward_demodulation,[],[f453,f43])).
% 0.23/0.53  fof(f453,plain,(
% 0.23/0.53    ( ! [X34] : (k2_xboole_0(sK3,k2_xboole_0(sK2,X34)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X34)) )),
% 0.23/0.53    inference(superposition,[],[f43,f184])).
% 0.23/0.53  fof(f184,plain,(
% 0.23/0.53    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 0.23/0.53    inference(forward_demodulation,[],[f170,f61])).
% 0.23/0.53  fof(f170,plain,(
% 0.23/0.53    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.23/0.53    inference(superposition,[],[f57,f27])).
% 0.23/0.53  fof(f49,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 0.23/0.53    inference(superposition,[],[f37,f33])).
% 0.23/0.53  fof(f2082,plain,(
% 0.23/0.53    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))) )),
% 0.23/0.53    inference(resolution,[],[f100,f29])).
% 0.23/0.53  fof(f100,plain,(
% 0.23/0.53    ( ! [X4,X2,X3] : (~r1_xboole_0(X4,X3) | ~r2_hidden(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) )),
% 0.23/0.53    inference(resolution,[],[f46,f41])).
% 0.23/0.53  fof(f41,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f20])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.23/0.53  fof(f1365,plain,(
% 0.23/0.53    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.23/0.53    inference(superposition,[],[f44,f1354])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (30082)------------------------------
% 0.23/0.53  % (30082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (30082)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (30082)Memory used [KB]: 11897
% 0.23/0.53  % (30082)Time elapsed: 0.119 s
% 0.23/0.53  % (30082)------------------------------
% 0.23/0.53  % (30082)------------------------------
% 0.23/0.53  % (30104)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.53  % (30090)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.53  % (30078)Success in time 0.16 s
%------------------------------------------------------------------------------
