%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 100 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f21,f87,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ sQ1_eqProxy(k1_xboole_0,k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sQ1_eqProxy(X1,X0)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( sQ1_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ sQ1_eqProxy(k4_xboole_0(X0,X1),k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f18,f19])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f87,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(resolution,[],[f84,f27])).

fof(f27,plain,(
    ! [X0] : sQ1_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f19])).

fof(f84,plain,(
    ! [X0] :
      ( ~ sQ1_eqProxy(X0,k1_xboole_0)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f83,f27])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ sQ1_eqProxy(X1,sK0)
      | ~ sQ1_eqProxy(X0,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f81,f20])).

fof(f20,plain,(
    ~ sQ1_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f14,f19])).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r2_xboole_0(k1_xboole_0,sK0)
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ~ r2_xboole_0(k1_xboole_0,X0)
        & k1_xboole_0 != X0 )
   => ( ~ r2_xboole_0(k1_xboole_0,sK0)
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ~ r2_xboole_0(k1_xboole_0,X0)
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => r2_xboole_0(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ sQ1_eqProxy(X0,k1_xboole_0)
      | sQ1_eqProxy(k1_xboole_0,sK0)
      | ~ sQ1_eqProxy(X1,sK0) ) ),
    inference(resolution,[],[f55,f15])).

fof(f15,plain,(
    ~ r2_xboole_0(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_xboole_0(X3,X1)
      | ~ r1_tarski(X2,X0)
      | ~ sQ1_eqProxy(X2,X3)
      | sQ1_eqProxy(X3,X1)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | sQ1_eqProxy(X0,X1)
      | r2_xboole_0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f17,f19])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | ~ sQ1_eqProxy(X2,X3)
      | ~ r1_tarski(X0,X2)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f19])).

fof(f21,plain,(
    ! [X0] : sQ1_eqProxy(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(equality_proxy_replacement,[],[f16,f19])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (21272)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.44  % (21272)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.45  % (21281)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f21,f87,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~sQ1_eqProxy(k1_xboole_0,k4_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(resolution,[],[f23,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (sQ1_eqProxy(X1,X0) | ~sQ1_eqProxy(X0,X1)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X1,X0] : (sQ1_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.45    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~sQ1_eqProxy(k4_xboole_0(X0,X1),k1_xboole_0) | r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(equality_proxy_replacement,[],[f18,f19])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 0.20/0.45    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    ~r1_tarski(k1_xboole_0,sK0)),
% 0.20/0.45    inference(resolution,[],[f84,f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0] : (sQ1_eqProxy(X0,X0)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f19])).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    ( ! [X0] : (~sQ1_eqProxy(X0,k1_xboole_0) | ~r1_tarski(X0,sK0)) )),
% 0.20/0.45    inference(resolution,[],[f83,f27])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~sQ1_eqProxy(X1,sK0) | ~sQ1_eqProxy(X0,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f81,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ~sQ1_eqProxy(k1_xboole_0,sK0)),
% 0.20/0.45    inference(equality_proxy_replacement,[],[f14,f19])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    k1_xboole_0 != sK0),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ~r2_xboole_0(k1_xboole_0,sK0) & k1_xboole_0 != sK0),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ? [X0] : (~r2_xboole_0(k1_xboole_0,X0) & k1_xboole_0 != X0) => (~r2_xboole_0(k1_xboole_0,sK0) & k1_xboole_0 != sK0)),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ? [X0] : (~r2_xboole_0(k1_xboole_0,X0) & k1_xboole_0 != X0)),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 0.20/0.45    inference(negated_conjecture,[],[f4])).
% 0.20/0.45  fof(f4,conjecture,(
% 0.20/0.45    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~sQ1_eqProxy(X0,k1_xboole_0) | sQ1_eqProxy(k1_xboole_0,sK0) | ~sQ1_eqProxy(X1,sK0)) )),
% 0.20/0.45    inference(resolution,[],[f55,f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ~r2_xboole_0(k1_xboole_0,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (r2_xboole_0(X3,X1) | ~r1_tarski(X2,X0) | ~sQ1_eqProxy(X2,X3) | sQ1_eqProxy(X3,X1) | ~sQ1_eqProxy(X0,X1)) )),
% 0.20/0.45    inference(resolution,[],[f26,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | sQ1_eqProxy(X0,X1) | r2_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(equality_proxy_replacement,[],[f17,f19])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,plain,(
% 0.20/0.45    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.20/0.45    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | ~sQ1_eqProxy(X2,X3) | ~r1_tarski(X0,X2) | ~sQ1_eqProxy(X0,X1)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f19])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ( ! [X0] : (sQ1_eqProxy(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.20/0.45    inference(equality_proxy_replacement,[],[f16,f19])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (21272)------------------------------
% 0.20/0.45  % (21272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (21272)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (21272)Memory used [KB]: 6140
% 0.20/0.45  % (21272)Time elapsed: 0.058 s
% 0.20/0.45  % (21272)------------------------------
% 0.20/0.45  % (21272)------------------------------
% 0.20/0.45  % (21264)Success in time 0.097 s
%------------------------------------------------------------------------------
