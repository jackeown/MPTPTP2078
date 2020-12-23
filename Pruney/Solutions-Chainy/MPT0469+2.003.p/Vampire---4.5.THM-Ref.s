%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 137 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 216 expanded)
%              Number of equality atoms :   50 (  95 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(subsumption_resolution,[],[f183,f146])).

fof(f146,plain,(
    o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0) ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f58,f136])).

fof(f136,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[],[f128,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f39,f33])).

fof(f33,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f128,plain,(
    v1_xboole_0(k1_relat_1(o_0_0_xboole_0)) ),
    inference(resolution,[],[f127,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f127,plain,(
    ! [X4] : ~ r2_hidden(X4,k1_relat_1(o_0_0_xboole_0)) ),
    inference(resolution,[],[f66,f83])).

fof(f83,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f82,f61])).

fof(f61,plain,(
    ! [X0] : o_0_0_xboole_0 = k3_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f35,f33,f33])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f82,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,o_0_0_xboole_0)) ),
    inference(resolution,[],[f49,f60])).

fof(f60,plain,(
    ! [X0] : r1_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f66,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f58,plain,
    ( o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f31,f33,f33,f33,f33])).

fof(f31,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f183,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(superposition,[],[f182,f63])).

fof(f63,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f182,plain,(
    o_0_0_xboole_0 = k2_xboole_0(k2_relat_1(o_0_0_xboole_0),o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f181,f138])).

fof(f138,plain,(
    o_0_0_xboole_0 = k2_relat_1(k4_relat_1(o_0_0_xboole_0)) ),
    inference(backward_demodulation,[],[f105,f136])).

fof(f105,plain,(
    k1_relat_1(o_0_0_xboole_0) = k2_relat_1(k4_relat_1(o_0_0_xboole_0)) ),
    inference(resolution,[],[f80,f59])).

fof(f59,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f181,plain,(
    k2_relat_1(k4_relat_1(o_0_0_xboole_0)) = k2_xboole_0(k2_relat_1(o_0_0_xboole_0),k2_relat_1(k4_relat_1(o_0_0_xboole_0))) ),
    inference(resolution,[],[f179,f59])).

fof(f179,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k2_relat_1(k4_relat_1(X0)) = k2_xboole_0(k2_relat_1(o_0_0_xboole_0),k2_relat_1(k4_relat_1(X0))) ) ),
    inference(resolution,[],[f175,f38])).

fof(f175,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k4_relat_1(X1)) = k2_xboole_0(k2_relat_1(o_0_0_xboole_0),k2_relat_1(k4_relat_1(X1))) ) ),
    inference(forward_demodulation,[],[f174,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f174,plain,(
    ! [X1] :
      ( k2_relat_1(k4_relat_1(X1)) = k2_xboole_0(k2_relat_1(k4_relat_1(X1)),k2_relat_1(o_0_0_xboole_0))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f172,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f172,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(o_0_0_xboole_0)) ) ),
    inference(forward_demodulation,[],[f171,f63])).

fof(f171,plain,(
    ! [X0] :
      ( k2_relat_1(k2_xboole_0(X0,o_0_0_xboole_0)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(o_0_0_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f167,f59])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f43,f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:16:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (8855)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.47  % (8847)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.48  % (8855)Refutation not found, incomplete strategy% (8855)------------------------------
% 0.21/0.48  % (8855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8855)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8855)Memory used [KB]: 10618
% 0.21/0.48  % (8855)Time elapsed: 0.047 s
% 0.21/0.48  % (8855)------------------------------
% 0.21/0.48  % (8855)------------------------------
% 0.21/0.49  % (8838)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (8838)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f183,f146])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    o_0_0_xboole_0 != o_0_0_xboole_0 | o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f58,f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f128,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f39,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    v1_xboole_0(k1_relat_1(o_0_0_xboole_0))),
% 0.21/0.50    inference(resolution,[],[f127,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(o_0_0_xboole_0))) )),
% 0.21/0.50    inference(resolution,[],[f66,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f82,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (o_0_0_xboole_0 = k3_xboole_0(X0,o_0_0_xboole_0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f35,f33,f33])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,o_0_0_xboole_0))) )),
% 0.21/0.50    inference(resolution,[],[f49,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(X0,o_0_0_xboole_0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f34,f33])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0) | o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0)),
% 0.21/0.50    inference(definition_unfolding,[],[f31,f33,f33,f33,f33])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(ennf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,negated_conjecture,(
% 0.21/0.50    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.21/0.50    inference(negated_conjecture,[],[f19])).
% 0.21/0.50  fof(f19,conjecture,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 0.21/0.50    inference(superposition,[],[f182,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (k2_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f37,f33])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    o_0_0_xboole_0 = k2_xboole_0(k2_relat_1(o_0_0_xboole_0),o_0_0_xboole_0)),
% 0.21/0.50    inference(forward_demodulation,[],[f181,f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    o_0_0_xboole_0 = k2_relat_1(k4_relat_1(o_0_0_xboole_0))),
% 0.21/0.50    inference(backward_demodulation,[],[f105,f136])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    k1_relat_1(o_0_0_xboole_0) = k2_relat_1(k4_relat_1(o_0_0_xboole_0))),
% 0.21/0.50    inference(resolution,[],[f80,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.50    inference(definition_unfolding,[],[f32,f33])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f42,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    k2_relat_1(k4_relat_1(o_0_0_xboole_0)) = k2_xboole_0(k2_relat_1(o_0_0_xboole_0),k2_relat_1(k4_relat_1(o_0_0_xboole_0)))),
% 0.21/0.50    inference(resolution,[],[f179,f59])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k2_relat_1(k4_relat_1(X0)) = k2_xboole_0(k2_relat_1(o_0_0_xboole_0),k2_relat_1(k4_relat_1(X0)))) )),
% 0.21/0.50    inference(resolution,[],[f175,f38])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_relat_1(X1) | k2_relat_1(k4_relat_1(X1)) = k2_xboole_0(k2_relat_1(o_0_0_xboole_0),k2_relat_1(k4_relat_1(X1)))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f174,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ( ! [X1] : (k2_relat_1(k4_relat_1(X1)) = k2_xboole_0(k2_relat_1(k4_relat_1(X1)),k2_relat_1(o_0_0_xboole_0)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(resolution,[],[f172,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(o_0_0_xboole_0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f171,f63])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(k2_xboole_0(X0,o_0_0_xboole_0)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(o_0_0_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(resolution,[],[f167,f59])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X1) | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(resolution,[],[f43,f38])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8838)------------------------------
% 0.21/0.50  % (8838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8838)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8838)Memory used [KB]: 6268
% 0.21/0.50  % (8838)Time elapsed: 0.058 s
% 0.21/0.50  % (8838)------------------------------
% 0.21/0.50  % (8838)------------------------------
% 0.21/0.50  % (8828)Success in time 0.14 s
%------------------------------------------------------------------------------
