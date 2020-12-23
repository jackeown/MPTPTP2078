%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:37 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 207 expanded)
%              Number of leaves         :   20 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  160 ( 439 expanded)
%              Number of equality atoms :   41 ( 139 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f71,f74,f280,f284])).

fof(f284,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl4_1
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f282])).

fof(f282,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f52,f231])).

fof(f231,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f156,f149])).

fof(f149,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f87,f58])).

% (26024)Refutation not found, incomplete strategy% (26024)------------------------------
% (26024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f58,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f46,f29])).

fof(f29,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

% (26024)Termination reason: Refutation not found, incomplete strategy
fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

% (26024)Memory used [KB]: 6140
fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

% (26024)Time elapsed: 0.125 s
% (26024)------------------------------
% (26024)------------------------------
fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_xboole_0,X0),X0)
      | k2_relat_1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f36,f58])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f156,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(resolution,[],[f87,f70])).

fof(f70,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_4
  <=> ! [X2] : ~ r2_hidden(X2,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f52,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f280,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl4_2 ),
    inference(trivial_inequality_removal,[],[f275])).

fof(f275,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_2 ),
    inference(superposition,[],[f56,f149])).

fof(f56,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f74,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f72,f28])).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f72,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_3 ),
    inference(resolution,[],[f67,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f67,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f71,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f62,f69,f65])).

fof(f62,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f60,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f19])).

fof(f19,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK0(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

fof(f60,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f58,f48])).

fof(f48,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f27,f54,f50])).

fof(f27,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.53  % (26011)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (26016)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (26016)Refutation not found, incomplete strategy% (26016)------------------------------
% 0.21/0.53  % (26016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26016)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26016)Memory used [KB]: 10618
% 0.21/0.53  % (26016)Time elapsed: 0.116 s
% 0.21/0.53  % (26016)------------------------------
% 0.21/0.53  % (26016)------------------------------
% 0.21/0.54  % (25999)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (26024)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.54  % (26011)Refutation found. Thanks to Tanya!
% 1.40/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f285,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(avatar_sat_refutation,[],[f57,f71,f74,f280,f284])).
% 1.40/0.54  fof(f284,plain,(
% 1.40/0.54    spl4_1 | ~spl4_4),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f283])).
% 1.40/0.54  fof(f283,plain,(
% 1.40/0.54    $false | (spl4_1 | ~spl4_4)),
% 1.40/0.54    inference(trivial_inequality_removal,[],[f282])).
% 1.40/0.54  fof(f282,plain,(
% 1.40/0.54    k1_xboole_0 != k1_xboole_0 | (spl4_1 | ~spl4_4)),
% 1.40/0.54    inference(superposition,[],[f52,f231])).
% 1.40/0.54  fof(f231,plain,(
% 1.40/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_4),
% 1.40/0.54    inference(forward_demodulation,[],[f156,f149])).
% 1.40/0.54  fof(f149,plain,(
% 1.40/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.40/0.54    inference(resolution,[],[f87,f58])).
% 1.40/0.54  % (26024)Refutation not found, incomplete strategy% (26024)------------------------------
% 1.40/0.54  % (26024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  fof(f58,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.40/0.54    inference(resolution,[],[f46,f29])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f2])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.40/0.54  fof(f46,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f38,f45])).
% 1.40/0.54  fof(f45,plain,(
% 1.40/0.54    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f30,f44])).
% 1.40/0.54  fof(f44,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f32,f43])).
% 1.40/0.54  fof(f43,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f39,f42])).
% 1.40/0.54  fof(f42,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f40,f41])).
% 1.40/0.54  fof(f41,plain,(
% 1.40/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f7])).
% 1.40/0.54  fof(f7,axiom,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.40/0.54  fof(f40,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f6])).
% 1.40/0.54  fof(f6,axiom,(
% 1.40/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.40/0.54  fof(f39,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.40/0.54  fof(f32,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f4])).
% 1.40/0.54  % (26024)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.40/0.54  
% 1.40/0.54  % (26024)Memory used [KB]: 6140
% 1.40/0.54  fof(f30,plain,(
% 1.40/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f3])).
% 1.40/0.54  % (26024)Time elapsed: 0.125 s
% 1.40/0.54  % (26024)------------------------------
% 1.40/0.54  % (26024)------------------------------
% 1.40/0.55  fof(f3,axiom,(
% 1.40/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f18])).
% 1.40/0.55  fof(f18,plain,(
% 1.40/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f8])).
% 1.40/0.55  fof(f8,axiom,(
% 1.40/0.55    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.40/0.55  fof(f87,plain,(
% 1.40/0.55    ( ! [X0] : (r2_hidden(sK1(k1_xboole_0,X0),X0) | k2_relat_1(k1_xboole_0) = X0) )),
% 1.40/0.55    inference(resolution,[],[f36,f58])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK1(X0,X1),X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f26])).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f24,plain,(
% 1.40/0.55    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.40/0.55    inference(rectify,[],[f21])).
% 1.40/0.55  fof(f21,plain,(
% 1.40/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f10])).
% 1.40/0.55  fof(f10,axiom,(
% 1.40/0.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.40/0.55  fof(f156,plain,(
% 1.40/0.55    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) | ~spl4_4),
% 1.40/0.55    inference(resolution,[],[f87,f70])).
% 1.40/0.55  fof(f70,plain,(
% 1.40/0.55    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k1_xboole_0))) ) | ~spl4_4),
% 1.40/0.55    inference(avatar_component_clause,[],[f69])).
% 1.40/0.55  fof(f69,plain,(
% 1.40/0.55    spl4_4 <=> ! [X2] : ~r2_hidden(X2,k1_relat_1(k1_xboole_0))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.40/0.55  fof(f52,plain,(
% 1.40/0.55    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl4_1),
% 1.40/0.55    inference(avatar_component_clause,[],[f50])).
% 1.40/0.55  fof(f50,plain,(
% 1.40/0.55    spl4_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.40/0.55  fof(f280,plain,(
% 1.40/0.55    spl4_2),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f279])).
% 1.40/0.55  fof(f279,plain,(
% 1.40/0.55    $false | spl4_2),
% 1.40/0.55    inference(trivial_inequality_removal,[],[f275])).
% 1.40/0.55  fof(f275,plain,(
% 1.40/0.55    k1_xboole_0 != k1_xboole_0 | spl4_2),
% 1.40/0.55    inference(superposition,[],[f56,f149])).
% 1.40/0.55  fof(f56,plain,(
% 1.40/0.55    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl4_2),
% 1.40/0.55    inference(avatar_component_clause,[],[f54])).
% 1.40/0.55  fof(f54,plain,(
% 1.40/0.55    spl4_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.40/0.55  fof(f74,plain,(
% 1.40/0.55    spl4_3),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f73])).
% 1.40/0.55  fof(f73,plain,(
% 1.40/0.55    $false | spl4_3),
% 1.40/0.55    inference(resolution,[],[f72,f28])).
% 1.40/0.55  fof(f28,plain,(
% 1.40/0.55    v1_xboole_0(k1_xboole_0)),
% 1.40/0.55    inference(cnf_transformation,[],[f1])).
% 1.40/0.55  fof(f1,axiom,(
% 1.40/0.55    v1_xboole_0(k1_xboole_0)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.40/0.55  fof(f72,plain,(
% 1.40/0.55    ~v1_xboole_0(k1_xboole_0) | spl4_3),
% 1.40/0.55    inference(resolution,[],[f67,f31])).
% 1.40/0.55  fof(f31,plain,(
% 1.40/0.55    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f15])).
% 1.40/0.55  fof(f15,plain,(
% 1.40/0.55    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f9])).
% 1.40/0.55  fof(f9,axiom,(
% 1.40/0.55    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.40/0.55  fof(f67,plain,(
% 1.40/0.55    ~v1_relat_1(k1_xboole_0) | spl4_3),
% 1.40/0.55    inference(avatar_component_clause,[],[f65])).
% 1.40/0.55  fof(f65,plain,(
% 1.40/0.55    spl4_3 <=> v1_relat_1(k1_xboole_0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.40/0.55  fof(f71,plain,(
% 1.40/0.55    ~spl4_3 | spl4_4),
% 1.40/0.55    inference(avatar_split_clause,[],[f62,f69,f65])).
% 1.40/0.55  fof(f62,plain,(
% 1.40/0.55    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 1.40/0.55    inference(resolution,[],[f60,f33])).
% 1.40/0.55  fof(f33,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r2_hidden(sK0(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f20])).
% 1.40/0.55  fof(f20,plain,(
% 1.40/0.55    ! [X0,X1] : (r2_hidden(sK0(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f19])).
% 1.40/0.55  fof(f19,plain,(
% 1.40/0.55    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK0(X1),k2_relat_1(X1)))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f17,plain,(
% 1.40/0.55    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(flattening,[],[f16])).
% 1.40/0.55  fof(f16,plain,(
% 1.40/0.55    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f11])).
% 1.40/0.55  fof(f11,axiom,(
% 1.40/0.55    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).
% 1.40/0.55  fof(f60,plain,(
% 1.40/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 1.40/0.55    inference(resolution,[],[f58,f48])).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.40/0.55    inference(equality_resolution,[],[f34])).
% 1.40/0.55  fof(f34,plain,(
% 1.40/0.55    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f26])).
% 1.40/0.55  fof(f57,plain,(
% 1.40/0.55    ~spl4_1 | ~spl4_2),
% 1.40/0.55    inference(avatar_split_clause,[],[f27,f54,f50])).
% 1.40/0.55  fof(f27,plain,(
% 1.40/0.55    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.40/0.55    inference(cnf_transformation,[],[f14])).
% 1.40/0.55  fof(f14,plain,(
% 1.40/0.55    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.40/0.55    inference(ennf_transformation,[],[f13])).
% 1.40/0.55  fof(f13,negated_conjecture,(
% 1.40/0.55    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 1.40/0.55    inference(negated_conjecture,[],[f12])).
% 1.40/0.55  fof(f12,conjecture,(
% 1.40/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (26011)------------------------------
% 1.40/0.55  % (26011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (26011)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (26011)Memory used [KB]: 6268
% 1.40/0.55  % (26011)Time elapsed: 0.134 s
% 1.40/0.55  % (26011)------------------------------
% 1.40/0.55  % (26011)------------------------------
% 1.40/0.55  % (25998)Success in time 0.187 s
%------------------------------------------------------------------------------
