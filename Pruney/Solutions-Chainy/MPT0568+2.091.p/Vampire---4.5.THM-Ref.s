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
% DateTime   : Thu Dec  3 12:50:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 (  89 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  173 ( 221 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f44,f48,f52,f56,f68,f78,f83,f151,f167,f187])).

fof(f187,plain,
    ( spl3_1
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl3_1
    | ~ spl3_25 ),
    inference(trivial_inequality_removal,[],[f182])).

fof(f182,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1
    | ~ spl3_25 ),
    inference(superposition,[],[f34,f166])).

fof(f166,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl3_25
  <=> ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f34,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f167,plain,
    ( spl3_25
    | ~ spl3_5
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f160,f149,f50,f165])).

fof(f50,plain,
    ( spl3_5
  <=> ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f149,plain,
    ( spl3_22
  <=> ! [X1,X0] : ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f160,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl3_5
    | ~ spl3_22 ),
    inference(resolution,[],[f150,f51])).

fof(f51,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f150,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( spl3_22
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f147,f81,f75,f66,f149])).

fof(f66,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f75,plain,
    ( spl3_11
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f81,plain,
    ( spl3_12
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f147,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f144,f77])).

fof(f77,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(resolution,[],[f67,f82])).

fof(f82,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f67,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f83,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f79,f54,f46,f81])).

fof(f46,plain,
    ( spl3_4
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f54,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f79,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f55,f47])).

fof(f47,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f78,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f73,f42,f37,f75])).

fof(f37,plain,
    ( spl3_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( spl3_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f73,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f43,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f43,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f68,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
            & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f56,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f52,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f32])).

fof(f21,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:55:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.43  % (728)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (732)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.44  % (731)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.44  % (732)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f188,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f35,f40,f44,f48,f52,f56,f68,f78,f83,f151,f167,f187])).
% 0.21/0.44  fof(f187,plain,(
% 0.21/0.44    spl3_1 | ~spl3_25),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.44  fof(f186,plain,(
% 0.21/0.44    $false | (spl3_1 | ~spl3_25)),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f182])).
% 0.21/0.44  fof(f182,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | (spl3_1 | ~spl3_25)),
% 0.21/0.44    inference(superposition,[],[f34,f166])).
% 0.21/0.44  fof(f166,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | ~spl3_25),
% 0.21/0.44    inference(avatar_component_clause,[],[f165])).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    spl3_25 <=> ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    spl3_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f167,plain,(
% 0.21/0.44    spl3_25 | ~spl3_5 | ~spl3_22),
% 0.21/0.44    inference(avatar_split_clause,[],[f160,f149,f50,f165])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl3_5 <=> ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    spl3_22 <=> ! [X1,X0] : ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl3_5 | ~spl3_22)),
% 0.21/0.44    inference(resolution,[],[f150,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) ) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f50])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) ) | ~spl3_22),
% 0.21/0.44    inference(avatar_component_clause,[],[f149])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    spl3_22 | ~spl3_9 | ~spl3_11 | ~spl3_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f147,f81,f75,f66,f149])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    spl3_9 <=> ! [X1,X0,X2] : (r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    spl3_11 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    spl3_12 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) ) | (~spl3_9 | ~spl3_11 | ~spl3_12)),
% 0.21/0.44    inference(subsumption_resolution,[],[f144,f77])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    v1_relat_1(k1_xboole_0) | ~spl3_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f75])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl3_9 | ~spl3_12)),
% 0.21/0.44    inference(resolution,[],[f67,f82])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f81])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl3_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f66])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    spl3_12 | ~spl3_4 | ~spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f79,f54,f46,f81])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl3_4 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    spl3_6 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_4 | ~spl3_6)),
% 0.21/0.44    inference(resolution,[],[f55,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f46])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f54])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    spl3_11 | ~spl3_2 | ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f73,f42,f37,f75])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl3_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl3_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    v1_relat_1(k1_xboole_0) | (~spl3_2 | ~spl3_3)),
% 0.21/0.44    inference(superposition,[],[f43,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f37])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f42])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl3_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f28,f66])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(rectify,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(nnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f54])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f50])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f46])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f42])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f37])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ~spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f32])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (732)------------------------------
% 0.21/0.44  % (732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (732)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (732)Memory used [KB]: 6140
% 0.21/0.44  % (732)Time elapsed: 0.006 s
% 0.21/0.44  % (732)------------------------------
% 0.21/0.44  % (732)------------------------------
% 0.21/0.44  % (720)Success in time 0.083 s
%------------------------------------------------------------------------------
