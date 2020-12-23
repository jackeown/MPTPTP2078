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
% DateTime   : Thu Dec  3 12:30:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  60 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 176 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f111])).

fof(f111,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f25,f15,f14,f98,f32])).

fof(f32,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(sK1,X5)
      | r2_xboole_0(X4,X5)
      | r2_xboole_0(sK1,X5)
      | ~ sQ3_eqProxy(sK0,X4) ) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X0,X1)
      | r2_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f18,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(sK1,X0)
      | ~ sQ3_eqProxy(sK0,X1)
      | r2_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f23,f13])).

fof(f13,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r1_tarski(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r1_tarski(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_xboole_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | r2_xboole_0(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f21])).

fof(f98,plain,
    ( ~ r2_xboole_0(sK1,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_3
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f14,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f21])).

fof(f108,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f13,f15,f99,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_xboole_0(X1,X2)
      | r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).

fof(f99,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:57:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (12788)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.44  % (12788)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f112,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f108,f111])).
% 0.22/0.44  fof(f111,plain,(
% 0.22/0.44    spl4_3),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f110])).
% 0.22/0.44  fof(f110,plain,(
% 0.22/0.44    $false | spl4_3),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f25,f15,f14,f98,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X4,X5] : (~r1_tarski(sK1,X5) | r2_xboole_0(X4,X5) | r2_xboole_0(sK1,X5) | ~sQ3_eqProxy(sK0,X4)) )),
% 0.22/0.44    inference(resolution,[],[f29,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X0,X1] : (sQ3_eqProxy(X0,X1) | r2_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(equality_proxy_replacement,[],[f18,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.44    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.44    inference(flattening,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.44    inference(nnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~sQ3_eqProxy(sK1,X0) | ~sQ3_eqProxy(sK0,X1) | r2_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(resolution,[],[f23,f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    r2_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f5])).
% 0.22/0.44  fof(f5,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.44    inference(negated_conjecture,[],[f3])).
% 0.22/0.44  fof(f3,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (~r2_xboole_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | r2_xboole_0(X1,X3)) )),
% 0.22/0.44    inference(equality_proxy_axiom,[],[f21])).
% 0.22/0.44  fof(f98,plain,(
% 0.22/0.44    ~r2_xboole_0(sK1,sK2) | spl4_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f97])).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    spl4_3 <=> r2_xboole_0(sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    r1_tarski(sK1,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ~r2_xboole_0(sK0,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.22/0.44    inference(equality_proxy_axiom,[],[f21])).
% 0.22/0.44  fof(f108,plain,(
% 0.22/0.44    ~spl4_3),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f104])).
% 0.22/0.44  fof(f104,plain,(
% 0.22/0.44    $false | ~spl4_3),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f13,f15,f99,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_xboole_0(X1,X2) | r2_xboole_0(X0,X2) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r2_xboole_0(X1,X2) | ~r2_xboole_0(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r2_xboole_0(X1,X2) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    r2_xboole_0(sK1,sK2) | ~spl4_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f97])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (12788)------------------------------
% 0.22/0.44  % (12788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (12788)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (12788)Memory used [KB]: 6140
% 0.22/0.44  % (12788)Time elapsed: 0.007 s
% 0.22/0.44  % (12788)------------------------------
% 0.22/0.44  % (12788)------------------------------
% 0.22/0.45  % (12782)Success in time 0.083 s
%------------------------------------------------------------------------------
