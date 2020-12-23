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
% DateTime   : Thu Dec  3 12:49:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 101 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :  211 ( 269 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f51,f55,f59,f63,f67,f83,f93,f132,f138,f145,f152])).

fof(f152,plain,
    ( spl4_1
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl4_1
    | ~ spl4_21 ),
    inference(trivial_inequality_removal,[],[f150])).

fof(f150,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_1
    | ~ spl4_21 ),
    inference(superposition,[],[f41,f144])).

fof(f144,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_21
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f41,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f145,plain,
    ( spl4_21
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f139,f136,f61,f143])).

fof(f61,plain,
    ( spl4_6
  <=> ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f136,plain,
    ( spl4_20
  <=> ! [X1,X0] : ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f139,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(resolution,[],[f137,f62])).

fof(f62,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f137,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,
    ( spl4_20
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f134,f130,f91,f44,f136])).

fof(f44,plain,
    ( spl4_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f91,plain,
    ( spl4_13
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f130,plain,
    ( spl4_19
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
        | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f134,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f133,f92])).

fof(f92,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),X0),k1_xboole_0)
        | ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) )
    | ~ spl4_2
    | ~ spl4_19 ),
    inference(resolution,[],[f131,f46])).

fof(f46,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f131,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X1)
        | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
        | ~ r2_hidden(X0,k9_relat_1(X1,X2)) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl4_19
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f128,f81,f57,f130])).

fof(f57,plain,
    ( spl4_5
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f81,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
        | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(resolution,[],[f82,f58])).

fof(f58,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f93,plain,
    ( spl4_13
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f89,f65,f53,f49,f91])).

fof(f49,plain,
    ( spl4_3
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f53,plain,
    ( spl4_4
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,
    ( spl4_7
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f89,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f88,f54])).

fof(f54,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f88,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f66,f50])).

fof(f50,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f83,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f67,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f33,f65])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f63,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f59,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f55,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f51,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f47,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f27,f44])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f42,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f39])).

fof(f26,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).

fof(f16,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (30209)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (30209)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f153,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f42,f47,f51,f55,f59,f63,f67,f83,f93,f132,f138,f145,f152])).
% 0.21/0.42  fof(f152,plain,(
% 0.21/0.42    spl4_1 | ~spl4_21),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.42  fof(f151,plain,(
% 0.21/0.42    $false | (spl4_1 | ~spl4_21)),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f150])).
% 0.21/0.42  fof(f150,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0 | (spl4_1 | ~spl4_21)),
% 0.21/0.42    inference(superposition,[],[f41,f144])).
% 0.21/0.42  fof(f144,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl4_21),
% 0.21/0.42    inference(avatar_component_clause,[],[f143])).
% 0.21/0.42  fof(f143,plain,(
% 0.21/0.42    spl4_21 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    spl4_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f145,plain,(
% 0.21/0.42    spl4_21 | ~spl4_6 | ~spl4_20),
% 0.21/0.42    inference(avatar_split_clause,[],[f139,f136,f61,f143])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl4_6 <=> ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f136,plain,(
% 0.21/0.42    spl4_20 <=> ! [X1,X0] : ~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.42  fof(f139,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl4_6 | ~spl4_20)),
% 0.21/0.42    inference(resolution,[],[f137,f62])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f61])).
% 0.21/0.42  fof(f137,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))) ) | ~spl4_20),
% 0.21/0.42    inference(avatar_component_clause,[],[f136])).
% 0.21/0.42  fof(f138,plain,(
% 0.21/0.42    spl4_20 | ~spl4_2 | ~spl4_13 | ~spl4_19),
% 0.21/0.42    inference(avatar_split_clause,[],[f134,f130,f91,f44,f136])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl4_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl4_13 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    spl4_19 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1) | ~v1_xboole_0(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))) ) | (~spl4_2 | ~spl4_13 | ~spl4_19)),
% 0.21/0.42    inference(subsumption_resolution,[],[f133,f92])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f91])).
% 0.21/0.42  fof(f133,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),X0),k1_xboole_0) | ~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))) ) | (~spl4_2 | ~spl4_19)),
% 0.21/0.42    inference(resolution,[],[f131,f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f44])).
% 0.21/0.42  fof(f131,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1) | ~r2_hidden(X0,k9_relat_1(X1,X2))) ) | ~spl4_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f130])).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    spl4_19 | ~spl4_5 | ~spl4_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f128,f81,f57,f130])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl4_5 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    spl4_11 <=> ! [X1,X0,X2] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.42  fof(f128,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1) | ~v1_xboole_0(X1)) ) | (~spl4_5 | ~spl4_11)),
% 0.21/0.42    inference(resolution,[],[f82,f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl4_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f57])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)) ) | ~spl4_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f81])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    spl4_13 | ~spl4_3 | ~spl4_4 | ~spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f89,f65,f53,f49,f91])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl4_3 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl4_4 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    spl4_7 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.42    inference(forward_demodulation,[],[f88,f54])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) ) | (~spl4_3 | ~spl4_7)),
% 0.21/0.42    inference(resolution,[],[f66,f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f49])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f65])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl4_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f35,f81])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(rectify,[],[f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(nnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f33,f65])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(rectify,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f31,f61])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl4_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f57])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl4_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f53])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f49])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f44])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ~spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f39])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,negated_conjecture,(
% 0.21/0.42    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    inference(negated_conjecture,[],[f8])).
% 0.21/0.42  fof(f8,conjecture,(
% 0.21/0.42    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (30209)------------------------------
% 0.21/0.42  % (30209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (30209)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (30209)Memory used [KB]: 10618
% 0.21/0.42  % (30209)Time elapsed: 0.008 s
% 0.21/0.42  % (30209)------------------------------
% 0.21/0.42  % (30209)------------------------------
% 0.21/0.42  % (30201)Success in time 0.065 s
%------------------------------------------------------------------------------
