%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  91 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 204 expanded)
%              Number of equality atoms :   30 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f86,f91])).

fof(f91,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f90,f83,f41])).

% (8233)Refutation not found, incomplete strategy% (8233)------------------------------
% (8233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f41,plain,
    ( spl4_1
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f83,plain,
    ( spl4_3
  <=> k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f90,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl4_3 ),
    inference(superposition,[],[f66,f85])).

fof(f85,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1))))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(sK3(sK0,X0),sK3(sK0,X0),sK3(sK0,X0),sK3(sK0,X0),sK3(sK0,X0)))
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f38,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(X2,X2,X2,X2,X2)) ) ),
    inference(definition_unfolding,[],[f20,f37])).

% (8233)Termination reason: Refutation not found, incomplete strategy

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f36])).

% (8233)Memory used [KB]: 10618
% (8233)Time elapsed: 0.120 s
fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f35])).

% (8233)------------------------------
% (8233)------------------------------
fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

fof(f86,plain,
    ( spl4_3
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f81,f46,f41,f83])).

fof(f46,plain,
    ( spl4_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f81,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1))))
    | spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f80,f43])).

fof(f43,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f80,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_relat_1(sK1))
        | k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK3(X0,k2_relat_1(sK1)),sK3(X0,k2_relat_1(sK1)),sK3(X0,k2_relat_1(sK1)),sK3(X0,k2_relat_1(sK1)),sK3(X0,k2_relat_1(sK1)))) )
    | ~ spl4_2 ),
    inference(resolution,[],[f79,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK1))
        | k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f71,f48])).

fof(f48,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(X0,k2_relat_1(X1))
      | k1_xboole_0 = k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(resolution,[],[f63,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f39,f59])).

fof(f59,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(X3,X4)
      | r1_xboole_0(X4,X3) ) ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f49,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:32:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (8225)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (8248)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (8241)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (8225)Refutation not found, incomplete strategy% (8225)------------------------------
% 0.21/0.53  % (8225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8225)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8225)Memory used [KB]: 1663
% 0.21/0.53  % (8225)Time elapsed: 0.108 s
% 0.21/0.53  % (8225)------------------------------
% 0.21/0.53  % (8225)------------------------------
% 0.21/0.53  % (8240)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (8232)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (8233)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (8241)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f44,f49,f86,f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    spl4_1 | ~spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f90,f83,f41])).
% 0.21/0.54  % (8233)Refutation not found, incomplete strategy% (8233)------------------------------
% 0.21/0.54  % (8233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    spl4_1 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    spl4_3 <=> k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl4_3),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_relat_1(sK1)) | ~spl4_3),
% 0.21/0.54    inference(superposition,[],[f66,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f83])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(sK3(sK0,X0),sK3(sK0,X0),sK3(sK0,X0),sK3(sK0,X0),sK3(sK0,X0))) | r1_tarski(sK0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f38,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.54    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(X2,X2,X2,X2,X2))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f20,f37])).
% 0.21/0.54  % (8233)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f23,f36])).
% 0.21/0.54  % (8233)Memory used [KB]: 10618
% 0.21/0.54  % (8233)Time elapsed: 0.120 s
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f25,f35])).
% 0.21/0.54  % (8233)------------------------------
% 0.21/0.54  % (8233)------------------------------
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f33,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0)) & v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0,X1] : ((~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0))) & v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    spl4_3 | spl4_1 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f81,f46,f41,f83])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    spl4_2 <=> v1_relat_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)),sK3(sK0,k2_relat_1(sK1)))) | (spl4_1 | ~spl4_2)),
% 0.21/0.54    inference(resolution,[],[f80,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ~r1_tarski(sK0,k2_relat_1(sK1)) | spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f41])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,k2_relat_1(sK1)) | k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK3(X0,k2_relat_1(sK1)),sK3(X0,k2_relat_1(sK1)),sK3(X0,k2_relat_1(sK1)),sK3(X0,k2_relat_1(sK1)),sK3(X0,k2_relat_1(sK1))))) ) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f79,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK1)) | k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(X0,X0,X0,X0,X0))) ) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f71,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    v1_relat_1(sK1) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f46])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(X0,k2_relat_1(X1)) | k1_xboole_0 = k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 0.21/0.54    inference(resolution,[],[f63,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k10_relat_1(X1,X0) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f39,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~r1_xboole_0(X3,X4) | r1_xboole_0(X4,X3)) )),
% 0.21/0.54    inference(resolution,[],[f50,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(superposition,[],[f26,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f30,f37])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f21,f46])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f22,f41])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (8241)------------------------------
% 0.21/0.54  % (8241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8241)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (8241)Memory used [KB]: 10746
% 0.21/0.54  % (8241)Time elapsed: 0.114 s
% 0.21/0.54  % (8241)------------------------------
% 0.21/0.54  % (8241)------------------------------
% 0.21/0.54  % (8230)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (8224)Success in time 0.176 s
%------------------------------------------------------------------------------
