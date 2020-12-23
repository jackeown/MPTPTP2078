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
% DateTime   : Thu Dec  3 12:49:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  88 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 203 expanded)
%              Number of equality atoms :   47 (  77 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f61,f73,f111,f119,f120])).

fof(f120,plain,
    ( sK0 != k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))
    | k1_xboole_0 != k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))
    | k1_xboole_0 = sK0 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f119,plain,
    ( spl4_11
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f114,f108,f116])).

fof(f116,plain,
    ( spl4_11
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f108,plain,
    ( spl4_10
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f114,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f113,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f113,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))
    | ~ spl4_10 ),
    inference(resolution,[],[f110,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(resolution,[],[f35,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f110,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f111,plain,
    ( spl4_10
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f106,f52,f37,f108])).

fof(f37,plain,
    ( spl4_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f52,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f106,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f87,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f87,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | r1_xboole_0(k1_relat_1(sK1),X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f31,f54])).

fof(f54,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f73,plain,
    ( spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f68,f58,f70])).

fof(f70,plain,
    ( spl4_6
  <=> sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f58,plain,
    ( spl4_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f67,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f67,plain,
    ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f33,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f61,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f56,f42,f58])).

fof(f42,plain,
    ( spl4_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f56,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f55,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f19,f52])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f50,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f47,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:37:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (31317)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (31325)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (31317)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f61,f73,f111,f119,f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    sK0 != k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) | k1_xboole_0 != k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) | k1_xboole_0 = sK0),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl4_11 | ~spl4_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f114,f108,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl4_11 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl4_10 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) | ~spl4_10),
% 0.21/0.51    inference(forward_demodulation,[],[f113,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) | ~spl4_10),
% 0.21/0.51    inference(resolution,[],[f110,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(resolution,[],[f35,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f28,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f108])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl4_10 | ~spl4_1 | ~spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f106,f52,f37,f108])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    spl4_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    spl4_4 <=> v1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl4_1 | ~spl4_4)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl4_1 | ~spl4_4)),
% 0.21/0.51    inference(superposition,[],[f87,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f37])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f31,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f52])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl4_6 | ~spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f68,f58,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl4_6 <=> sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl4_5 <=> k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) | ~spl4_5),
% 0.21/0.51    inference(forward_demodulation,[],[f67,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0) | ~spl4_5),
% 0.21/0.51    inference(superposition,[],[f33,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) | ~spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f27,f26])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl4_5 | ~spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f56,f42,f58])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    spl4_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) | ~spl4_2),
% 0.21/0.51    inference(resolution,[],[f32,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f42])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f19,f52])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ~spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f20,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    spl4_3 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f42])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f22,f37])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (31317)------------------------------
% 0.21/0.51  % (31317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31317)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (31317)Memory used [KB]: 10746
% 0.21/0.51  % (31317)Time elapsed: 0.075 s
% 0.21/0.51  % (31317)------------------------------
% 0.21/0.51  % (31317)------------------------------
% 0.21/0.51  % (31298)Success in time 0.144 s
%------------------------------------------------------------------------------
