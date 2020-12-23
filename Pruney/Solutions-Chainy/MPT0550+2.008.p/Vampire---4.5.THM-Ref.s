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
% DateTime   : Thu Dec  3 12:49:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 105 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  155 ( 287 expanded)
%              Number of equality atoms :   35 (  86 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f59,f78,f85,f88])).

fof(f88,plain,
    ( spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f86,f82,f46])).

fof(f46,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f82,plain,
    ( spl3_9
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f86,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_9 ),
    inference(resolution,[],[f83,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f83,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f80,f76,f42,f82])).

fof(f42,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f76,plain,
    ( spl3_8
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f80,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | v1_xboole_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f77,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f77,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f72,f57,f76])).

fof(f57,plain,
    ( spl3_5
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f72,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl3_5 ),
    inference(resolution,[],[f36,f62])).

fof(f62,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f60,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f60,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)))
    | ~ spl3_5 ),
    inference(resolution,[],[f58,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f30,f28])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f58,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f55,f50,f38,f57])).

fof(f38,plain,
    ( spl3_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( spl3_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f55,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f53,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f53,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | r1_xboole_0(k1_relat_1(sK1),X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f32,f51])).

fof(f51,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f52,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK1,sK0)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f48,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f24,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f25,f38])).

fof(f25,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:06:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (32621)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (32621)Refutation not found, incomplete strategy% (32621)------------------------------
% 0.21/0.53  % (32621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32621)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32621)Memory used [KB]: 10618
% 0.21/0.53  % (32621)Time elapsed: 0.108 s
% 0.21/0.53  % (32621)------------------------------
% 0.21/0.53  % (32621)------------------------------
% 0.21/0.54  % (32637)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (32629)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (32637)Refutation not found, incomplete strategy% (32637)------------------------------
% 0.21/0.54  % (32637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32637)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32637)Memory used [KB]: 6268
% 0.21/0.54  % (32637)Time elapsed: 0.121 s
% 0.21/0.54  % (32637)------------------------------
% 0.21/0.54  % (32637)------------------------------
% 0.21/0.54  % (32629)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f59,f78,f85,f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    spl3_3 | ~spl3_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f86,f82,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    spl3_3 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl3_9 <=> v1_xboole_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | ~spl3_9),
% 0.21/0.54    inference(resolution,[],[f83,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | ~spl3_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f82])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    spl3_9 | ~spl3_2 | ~spl3_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f80,f76,f42,f82])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    spl3_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    spl3_8 <=> r1_xboole_0(sK0,k1_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ~r1_tarski(sK0,k1_relat_1(sK1)) | v1_xboole_0(sK0) | ~spl3_8),
% 0.21/0.54    inference(resolution,[],[f77,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl3_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f76])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    spl3_8 | ~spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f72,f57,f76])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    spl3_5 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl3_5),
% 0.21/0.55    inference(resolution,[],[f36,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))))) ) | ~spl3_5),
% 0.21/0.55    inference(forward_demodulation,[],[f60,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f27,f28,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)))) ) | ~spl3_5),
% 0.21/0.55    inference(resolution,[],[f58,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f30,f28])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl3_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f57])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f29,f28])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    spl3_5 | ~spl3_1 | ~spl3_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f55,f50,f38,f57])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    spl3_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    spl3_4 <=> v1_relat_1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl3_1 | ~spl3_4)),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl3_1 | ~spl3_4)),
% 0.21/0.55    inference(superposition,[],[f53,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl3_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f38])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl3_4),
% 0.21/0.55    inference(resolution,[],[f32,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    v1_relat_1(sK1) | ~spl3_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f50])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    spl3_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f22,f50])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    v1_relat_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.55    inference(negated_conjecture,[],[f7])).
% 0.21/0.55  fof(f7,conjecture,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ~spl3_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f23,f46])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f24,f42])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    spl3_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f25,f38])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (32629)------------------------------
% 0.21/0.55  % (32629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32629)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (32629)Memory used [KB]: 10746
% 0.21/0.55  % (32629)Time elapsed: 0.122 s
% 0.21/0.55  % (32629)------------------------------
% 0.21/0.55  % (32629)------------------------------
% 0.21/0.55  % (32609)Success in time 0.185 s
%------------------------------------------------------------------------------
