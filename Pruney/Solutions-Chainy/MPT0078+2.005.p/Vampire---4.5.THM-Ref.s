%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:47 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 899 expanded)
%              Number of leaves         :   15 ( 260 expanded)
%              Depth                    :   24
%              Number of atoms          :  143 (2349 expanded)
%              Number of equality atoms :   69 ( 684 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f836,plain,(
    $false ),
    inference(subsumption_resolution,[],[f835,f33])).

fof(f33,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f835,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f811,f84])).

fof(f84,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f49,f70])).

fof(f70,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f60,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = X0 ) ),
    inference(resolution,[],[f59,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f59,plain,(
    v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f51,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f31,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f31,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f811,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f147,f809])).

fof(f809,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f808,f129])).

fof(f129,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f113,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f113,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f93,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f93,plain,(
    sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f49,f70])).

fof(f808,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK1) ),
    inference(forward_demodulation,[],[f789,f36])).

fof(f789,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,k1_xboole_0),sK1) ),
    inference(superposition,[],[f250,f745])).

fof(f745,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f729,f168])).

fof(f168,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f160,f46])).

fof(f160,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[],[f156,f36])).

fof(f156,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f49,f142])).

fof(f142,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f97,f32])).

fof(f32,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f73,f47])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f69,f70])).

fof(f69,plain,(
    ! [X0] :
      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(resolution,[],[f60,f38])).

fof(f729,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK2),sK1) ),
    inference(superposition,[],[f249,f54])).

fof(f54,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f30,f36])).

fof(f30,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f249,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(sK1,X0),sK1) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK1) ),
    inference(forward_demodulation,[],[f242,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f242,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(sK1,X0),sK1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,sK1),k4_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f44,f228])).

fof(f228,plain,(
    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f105,f112])).

fof(f112,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f111,f100])).

fof(f100,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f49,f77])).

fof(f77,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f72,f70])).

fof(f72,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f60,f64])).

fof(f64,plain,(
    v1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f53,f38])).

fof(f53,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f40,f40])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(resolution,[],[f32,f47])).

fof(f111,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f106,f36])).

fof(f106,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f46,f77])).

fof(f105,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),X3)) ),
    inference(superposition,[],[f45,f77])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f250,plain,(
    ! [X1] : k4_xboole_0(k2_xboole_0(X1,sK1),sK1) = k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),sK1) ),
    inference(forward_demodulation,[],[f243,f44])).

fof(f243,plain,(
    ! [X1] : k4_xboole_0(k2_xboole_0(X1,sK1),sK1) = k2_xboole_0(k4_xboole_0(X1,sK1),k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[],[f44,f228])).

fof(f147,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f49,f142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:07:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (9917)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (9934)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (9926)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (9932)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (9934)Refutation not found, incomplete strategy% (9934)------------------------------
% 0.21/0.56  % (9934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9934)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9934)Memory used [KB]: 10618
% 0.21/0.56  % (9934)Time elapsed: 0.123 s
% 0.21/0.56  % (9934)------------------------------
% 0.21/0.56  % (9934)------------------------------
% 0.21/0.56  % (9932)Refutation not found, incomplete strategy% (9932)------------------------------
% 0.21/0.56  % (9932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9932)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9932)Memory used [KB]: 6140
% 0.21/0.56  % (9932)Time elapsed: 0.081 s
% 0.21/0.56  % (9932)------------------------------
% 0.21/0.56  % (9932)------------------------------
% 0.21/0.57  % (9924)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (9923)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.51/0.58  % (9922)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.78/0.59  % (9920)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.78/0.59  % (9940)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.78/0.60  % (9919)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.78/0.60  % (9919)Refutation not found, incomplete strategy% (9919)------------------------------
% 1.78/0.60  % (9919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (9919)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (9919)Memory used [KB]: 10618
% 1.78/0.60  % (9919)Time elapsed: 0.160 s
% 1.78/0.60  % (9919)------------------------------
% 1.78/0.60  % (9919)------------------------------
% 1.78/0.60  % (9918)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.78/0.60  % (9939)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.78/0.60  % (9939)Refutation not found, incomplete strategy% (9939)------------------------------
% 1.78/0.60  % (9939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (9939)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (9939)Memory used [KB]: 10746
% 1.78/0.60  % (9939)Time elapsed: 0.170 s
% 1.78/0.60  % (9939)------------------------------
% 1.78/0.60  % (9939)------------------------------
% 1.78/0.60  % (9943)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.78/0.61  % (9931)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.78/0.61  % (9946)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.78/0.61  % (9929)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.78/0.61  % (9935)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.78/0.61  % (9927)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.78/0.61  % (9938)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.78/0.61  % (9933)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.78/0.61  % (9928)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.78/0.61  % (9938)Refutation not found, incomplete strategy% (9938)------------------------------
% 1.78/0.61  % (9938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (9938)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.61  
% 1.78/0.61  % (9938)Memory used [KB]: 1663
% 1.78/0.61  % (9938)Time elapsed: 0.181 s
% 1.78/0.61  % (9938)------------------------------
% 1.78/0.61  % (9938)------------------------------
% 1.78/0.61  % (9940)Refutation not found, incomplete strategy% (9940)------------------------------
% 1.78/0.61  % (9940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (9940)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.61  
% 1.78/0.61  % (9940)Memory used [KB]: 1791
% 1.78/0.61  % (9940)Time elapsed: 0.148 s
% 1.78/0.61  % (9940)------------------------------
% 1.78/0.61  % (9940)------------------------------
% 1.78/0.62  % (9928)Refutation not found, incomplete strategy% (9928)------------------------------
% 1.78/0.62  % (9928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.62  % (9941)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.78/0.62  % (9917)Refutation found. Thanks to Tanya!
% 1.78/0.62  % SZS status Theorem for theBenchmark
% 1.78/0.62  % (9930)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.78/0.62  % SZS output start Proof for theBenchmark
% 1.78/0.62  fof(f836,plain,(
% 1.78/0.62    $false),
% 1.78/0.62    inference(subsumption_resolution,[],[f835,f33])).
% 1.78/0.62  fof(f33,plain,(
% 1.78/0.62    sK0 != sK2),
% 1.78/0.62    inference(cnf_transformation,[],[f23])).
% 1.78/0.62  fof(f23,plain,(
% 1.78/0.62    sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 1.78/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22])).
% 1.78/0.62  fof(f22,plain,(
% 1.78/0.62    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1))),
% 1.78/0.62    introduced(choice_axiom,[])).
% 1.78/0.62  fof(f19,plain,(
% 1.78/0.62    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 1.78/0.62    inference(flattening,[],[f18])).
% 1.78/0.62  fof(f18,plain,(
% 1.78/0.62    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 1.78/0.62    inference(ennf_transformation,[],[f16])).
% 1.78/0.62  fof(f16,negated_conjecture,(
% 1.78/0.62    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.78/0.62    inference(negated_conjecture,[],[f15])).
% 1.78/0.62  fof(f15,conjecture,(
% 1.78/0.62    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 1.78/0.62  fof(f835,plain,(
% 1.78/0.62    sK0 = sK2),
% 1.78/0.62    inference(forward_demodulation,[],[f811,f84])).
% 1.78/0.62  fof(f84,plain,(
% 1.78/0.62    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 1.78/0.62    inference(superposition,[],[f49,f70])).
% 1.78/0.62  fof(f70,plain,(
% 1.78/0.62    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.78/0.62    inference(resolution,[],[f60,f43])).
% 1.78/0.62  fof(f43,plain,(
% 1.78/0.62    v1_xboole_0(k1_xboole_0)),
% 1.78/0.62    inference(cnf_transformation,[],[f4])).
% 1.78/0.62  fof(f4,axiom,(
% 1.78/0.62    v1_xboole_0(k1_xboole_0)),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.78/0.62  fof(f60,plain,(
% 1.78/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = X0) )),
% 1.78/0.62    inference(resolution,[],[f59,f42])).
% 1.78/0.62  fof(f42,plain,(
% 1.78/0.62    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f21])).
% 1.78/0.62  fof(f21,plain,(
% 1.78/0.62    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.78/0.62    inference(ennf_transformation,[],[f14])).
% 1.78/0.62  fof(f14,axiom,(
% 1.78/0.62    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.78/0.62  fof(f59,plain,(
% 1.78/0.62    v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.78/0.62    inference(resolution,[],[f51,f38])).
% 1.78/0.62  fof(f38,plain,(
% 1.78/0.62    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f29])).
% 1.78/0.62  fof(f29,plain,(
% 1.78/0.62    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.78/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 1.78/0.62  fof(f28,plain,(
% 1.78/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.78/0.62    introduced(choice_axiom,[])).
% 1.78/0.62  fof(f27,plain,(
% 1.78/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.78/0.62    inference(rectify,[],[f26])).
% 1.78/0.62  fof(f26,plain,(
% 1.78/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.78/0.62    inference(nnf_transformation,[],[f3])).
% 1.78/0.62  fof(f3,axiom,(
% 1.78/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.78/0.62  fof(f51,plain,(
% 1.78/0.62    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) )),
% 1.78/0.62    inference(resolution,[],[f31,f47])).
% 1.78/0.62  fof(f47,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.78/0.62    inference(definition_unfolding,[],[f35,f40])).
% 1.78/0.62  fof(f40,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.78/0.62    inference(cnf_transformation,[],[f12])).
% 1.78/0.62  fof(f12,axiom,(
% 1.78/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.78/0.62  fof(f35,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.78/0.62    inference(cnf_transformation,[],[f25])).
% 1.78/0.62  fof(f25,plain,(
% 1.78/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.78/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f24])).
% 1.78/0.62  fof(f24,plain,(
% 1.78/0.62    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.78/0.62    introduced(choice_axiom,[])).
% 1.78/0.62  fof(f20,plain,(
% 1.78/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.78/0.62    inference(ennf_transformation,[],[f17])).
% 1.78/0.62  fof(f17,plain,(
% 1.78/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.78/0.62    inference(rectify,[],[f5])).
% 1.78/0.62  fof(f5,axiom,(
% 1.78/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.78/0.62  fof(f31,plain,(
% 1.78/0.62    r1_xboole_0(sK0,sK1)),
% 1.78/0.62    inference(cnf_transformation,[],[f23])).
% 1.78/0.62  fof(f49,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.78/0.62    inference(definition_unfolding,[],[f39,f40])).
% 1.78/0.62  fof(f39,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.78/0.62    inference(cnf_transformation,[],[f13])).
% 1.78/0.62  fof(f13,axiom,(
% 1.78/0.62    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.78/0.62  fof(f811,plain,(
% 1.78/0.62    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 1.78/0.62    inference(backward_demodulation,[],[f147,f809])).
% 1.78/0.62  fof(f809,plain,(
% 1.78/0.62    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1)),
% 1.78/0.62    inference(forward_demodulation,[],[f808,f129])).
% 1.78/0.62  fof(f129,plain,(
% 1.78/0.62    sK0 = k2_xboole_0(k1_xboole_0,sK0)),
% 1.78/0.62    inference(superposition,[],[f113,f46])).
% 1.78/0.62  fof(f46,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.78/0.62    inference(cnf_transformation,[],[f8])).
% 1.78/0.62  fof(f8,axiom,(
% 1.78/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.78/0.62  fof(f113,plain,(
% 1.78/0.62    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))),
% 1.78/0.62    inference(superposition,[],[f93,f36])).
% 1.78/0.62  fof(f36,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f1])).
% 1.78/0.62  fof(f1,axiom,(
% 1.78/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.78/0.62  fof(f93,plain,(
% 1.78/0.62    sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)),
% 1.78/0.62    inference(superposition,[],[f49,f70])).
% 1.78/0.62  fof(f808,plain,(
% 1.78/0.62    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK0),sK1)),
% 1.78/0.62    inference(forward_demodulation,[],[f789,f36])).
% 1.78/0.62  fof(f789,plain,(
% 1.78/0.62    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,k1_xboole_0),sK1)),
% 1.78/0.62    inference(superposition,[],[f250,f745])).
% 1.78/0.62  fof(f745,plain,(
% 1.78/0.62    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 1.78/0.62    inference(forward_demodulation,[],[f729,f168])).
% 1.78/0.62  fof(f168,plain,(
% 1.78/0.62    sK2 = k2_xboole_0(k1_xboole_0,sK2)),
% 1.78/0.62    inference(superposition,[],[f160,f46])).
% 1.78/0.62  fof(f160,plain,(
% 1.78/0.62    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k1_xboole_0))),
% 1.78/0.62    inference(superposition,[],[f156,f36])).
% 1.78/0.62  fof(f156,plain,(
% 1.78/0.62    sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0)),
% 1.78/0.62    inference(superposition,[],[f49,f142])).
% 1.78/0.62  fof(f142,plain,(
% 1.78/0.62    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 1.78/0.62    inference(resolution,[],[f97,f32])).
% 1.78/0.62  fof(f32,plain,(
% 1.78/0.62    r1_xboole_0(sK2,sK1)),
% 1.78/0.62    inference(cnf_transformation,[],[f23])).
% 1.78/0.62  fof(f97,plain,(
% 1.78/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.78/0.62    inference(resolution,[],[f73,f47])).
% 1.78/0.62  fof(f73,plain,(
% 1.78/0.62    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.78/0.62    inference(backward_demodulation,[],[f69,f70])).
% 1.78/0.62  fof(f69,plain,(
% 1.78/0.62    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = X0 | r2_hidden(sK4(X0),X0)) )),
% 1.78/0.62    inference(resolution,[],[f60,f38])).
% 1.78/0.62  fof(f729,plain,(
% 1.78/0.62    k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) = k4_xboole_0(k2_xboole_0(k1_xboole_0,sK2),sK1)),
% 1.78/0.62    inference(superposition,[],[f249,f54])).
% 1.78/0.62  fof(f54,plain,(
% 1.78/0.62    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)),
% 1.78/0.62    inference(superposition,[],[f30,f36])).
% 1.78/0.62  fof(f30,plain,(
% 1.78/0.62    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 1.78/0.62    inference(cnf_transformation,[],[f23])).
% 1.78/0.62  fof(f249,plain,(
% 1.78/0.62    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK1,X0),sK1) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK1)) )),
% 1.78/0.62    inference(forward_demodulation,[],[f242,f44])).
% 1.78/0.62  fof(f44,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 1.78/0.62    inference(cnf_transformation,[],[f11])).
% 1.78/0.62  fof(f11,axiom,(
% 1.78/0.62    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 1.78/0.62  fof(f242,plain,(
% 1.78/0.62    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK1,X0),sK1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,sK1),k4_xboole_0(X0,sK1))) )),
% 1.78/0.62    inference(superposition,[],[f44,f228])).
% 1.78/0.62  fof(f228,plain,(
% 1.78/0.62    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1)),
% 1.78/0.62    inference(superposition,[],[f105,f112])).
% 1.78/0.62  fof(f112,plain,(
% 1.78/0.62    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1)),
% 1.78/0.62    inference(forward_demodulation,[],[f111,f100])).
% 1.78/0.62  fof(f100,plain,(
% 1.78/0.62    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),
% 1.78/0.62    inference(superposition,[],[f49,f77])).
% 1.78/0.62  fof(f77,plain,(
% 1.78/0.62    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.78/0.62    inference(forward_demodulation,[],[f72,f70])).
% 1.78/0.62  fof(f72,plain,(
% 1.78/0.62    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.78/0.62    inference(resolution,[],[f60,f64])).
% 1.78/0.62  fof(f64,plain,(
% 1.78/0.62    v1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.78/0.62    inference(resolution,[],[f53,f38])).
% 1.78/0.62  fof(f53,plain,(
% 1.78/0.62    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) )),
% 1.78/0.62    inference(forward_demodulation,[],[f52,f50])).
% 1.78/0.62  fof(f50,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.78/0.62    inference(definition_unfolding,[],[f41,f40,f40])).
% 1.78/0.62  fof(f41,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f2])).
% 1.78/0.62  fof(f2,axiom,(
% 1.78/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.78/0.62  fof(f52,plain,(
% 1.78/0.62    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) )),
% 1.78/0.62    inference(resolution,[],[f32,f47])).
% 1.78/0.62  fof(f111,plain,(
% 1.78/0.62    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1)),
% 1.78/0.62    inference(forward_demodulation,[],[f106,f36])).
% 1.78/0.62  fof(f106,plain,(
% 1.78/0.62    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 1.78/0.62    inference(superposition,[],[f46,f77])).
% 1.78/0.62  fof(f105,plain,(
% 1.78/0.62    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),X3))) )),
% 1.78/0.62    inference(superposition,[],[f45,f77])).
% 1.78/0.62  fof(f45,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.78/0.62    inference(cnf_transformation,[],[f10])).
% 1.78/0.62  fof(f10,axiom,(
% 1.78/0.62    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.78/0.62  fof(f250,plain,(
% 1.78/0.62    ( ! [X1] : (k4_xboole_0(k2_xboole_0(X1,sK1),sK1) = k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),sK1)) )),
% 1.78/0.62    inference(forward_demodulation,[],[f243,f44])).
% 1.78/0.62  fof(f243,plain,(
% 1.78/0.62    ( ! [X1] : (k4_xboole_0(k2_xboole_0(X1,sK1),sK1) = k2_xboole_0(k4_xboole_0(X1,sK1),k4_xboole_0(k1_xboole_0,sK1))) )),
% 1.78/0.62    inference(superposition,[],[f44,f228])).
% 1.78/0.62  fof(f147,plain,(
% 1.78/0.62    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))),
% 1.78/0.62    inference(superposition,[],[f49,f142])).
% 1.78/0.62  % SZS output end Proof for theBenchmark
% 1.78/0.62  % (9917)------------------------------
% 1.78/0.62  % (9917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.62  % (9917)Termination reason: Refutation
% 1.78/0.62  
% 1.78/0.62  % (9917)Memory used [KB]: 2430
% 1.78/0.62  % (9917)Time elapsed: 0.135 s
% 1.78/0.62  % (9917)------------------------------
% 1.78/0.62  % (9917)------------------------------
% 1.78/0.62  % (9916)Success in time 0.255 s
%------------------------------------------------------------------------------
