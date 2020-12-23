%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 (  99 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :    6
%              Number of atoms          :  163 ( 274 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f42,f46,f50,f54,f63,f71,f79,f86,f89])).

fof(f89,plain,
    ( spl3_1
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl3_1
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f87,f27])).

fof(f27,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f87,plain,
    ( k1_xboole_0 = k7_relat_1(sK0,sK1)
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(resolution,[],[f85,f78])).

fof(f78,plain,
    ( r1_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_11
  <=> r1_xboole_0(k1_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f86,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f82,f52,f35,f84])).

fof(f35,plain,
    ( spl3_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f52,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f53,f37])).

fof(f37,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f79,plain,
    ( spl3_11
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f72,f68,f61,f76])).

fof(f61,plain,
    ( spl3_9
  <=> ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f68,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1),k3_xboole_0(X1,X0))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f72,plain,
    ( r1_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(resolution,[],[f69,f62])).

fof(f62,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,k1_relat_1(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),k3_xboole_0(X1,X0))
        | r1_xboole_0(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f71,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f66,f48,f40,f68])).

fof(f40,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f66,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK2(X2,X3),k3_xboole_0(X3,X2))
        | r1_xboole_0(X2,X3) )
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f49,f41])).

fof(f41,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f63,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f59,f44,f30,f61])).

fof(f30,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f59,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,k1_relat_1(sK0)))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,
    ( r1_xboole_0(sK1,k1_relat_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f45,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f54,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k7_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,sK1)
    & r1_xboole_0(sK1,k1_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != k7_relat_1(X0,X1)
            & r1_xboole_0(X1,k1_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(sK0,X1)
          & r1_xboole_0(X1,k1_relat_1(sK0)) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( k1_xboole_0 != k7_relat_1(sK0,X1)
        & r1_xboole_0(X1,k1_relat_1(sK0)) )
   => ( k1_xboole_0 != k7_relat_1(sK0,sK1)
      & r1_xboole_0(sK1,k1_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(X0,X1)
          & r1_xboole_0(X1,k1_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r1_xboole_0(X1,k1_relat_1(X0))
           => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    r1_xboole_0(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f25])).

fof(f18,plain,(
    k1_xboole_0 != k7_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:23:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.41  % (25901)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (25902)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (25901)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f90,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f28,f33,f38,f42,f46,f50,f54,f63,f71,f79,f86,f89])).
% 0.22/0.42  fof(f89,plain,(
% 0.22/0.42    spl3_1 | ~spl3_11 | ~spl3_12),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f88])).
% 0.22/0.42  fof(f88,plain,(
% 0.22/0.42    $false | (spl3_1 | ~spl3_11 | ~spl3_12)),
% 0.22/0.42    inference(subsumption_resolution,[],[f87,f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    k1_xboole_0 != k7_relat_1(sK0,sK1) | spl3_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f25])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    spl3_1 <=> k1_xboole_0 = k7_relat_1(sK0,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.42  fof(f87,plain,(
% 0.22/0.42    k1_xboole_0 = k7_relat_1(sK0,sK1) | (~spl3_11 | ~spl3_12)),
% 0.22/0.42    inference(resolution,[],[f85,f78])).
% 0.22/0.42  fof(f78,plain,(
% 0.22/0.42    r1_xboole_0(k1_relat_1(sK0),sK1) | ~spl3_11),
% 0.22/0.42    inference(avatar_component_clause,[],[f76])).
% 0.22/0.42  fof(f76,plain,(
% 0.22/0.42    spl3_11 <=> r1_xboole_0(k1_relat_1(sK0),sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.42  fof(f85,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | ~spl3_12),
% 0.22/0.42    inference(avatar_component_clause,[],[f84])).
% 0.22/0.42  fof(f84,plain,(
% 0.22/0.42    spl3_12 <=> ! [X0] : (~r1_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.42  fof(f86,plain,(
% 0.22/0.42    spl3_12 | ~spl3_3 | ~spl3_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f82,f52,f35,f84])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    spl3_3 <=> v1_relat_1(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    spl3_7 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.42  fof(f82,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | (~spl3_3 | ~spl3_7)),
% 0.22/0.42    inference(resolution,[],[f53,f37])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    v1_relat_1(sK0) | ~spl3_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f35])).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = k1_xboole_0) ) | ~spl3_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f52])).
% 0.22/0.42  fof(f79,plain,(
% 0.22/0.42    spl3_11 | ~spl3_9 | ~spl3_10),
% 0.22/0.42    inference(avatar_split_clause,[],[f72,f68,f61,f76])).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    spl3_9 <=> ! [X0] : ~r2_hidden(X0,k3_xboole_0(sK1,k1_relat_1(sK0)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.42  fof(f68,plain,(
% 0.22/0.42    spl3_10 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X1,X0)) | r1_xboole_0(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.42  fof(f72,plain,(
% 0.22/0.42    r1_xboole_0(k1_relat_1(sK0),sK1) | (~spl3_9 | ~spl3_10)),
% 0.22/0.42    inference(resolution,[],[f69,f62])).
% 0.22/0.42  fof(f62,plain,(
% 0.22/0.42    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k1_relat_1(sK0)))) ) | ~spl3_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f61])).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X1,X0)) | r1_xboole_0(X0,X1)) ) | ~spl3_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f68])).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    spl3_10 | ~spl3_4 | ~spl3_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f66,f48,f40,f68])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    spl3_6 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.42  fof(f66,plain,(
% 0.22/0.42    ( ! [X2,X3] : (r2_hidden(sK2(X2,X3),k3_xboole_0(X3,X2)) | r1_xboole_0(X2,X3)) ) | (~spl3_4 | ~spl3_6)),
% 0.22/0.42    inference(superposition,[],[f49,f41])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f40])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) ) | ~spl3_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f48])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    spl3_9 | ~spl3_2 | ~spl3_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f59,f44,f30,f61])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    spl3_2 <=> r1_xboole_0(sK1,k1_relat_1(sK0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    spl3_5 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k1_relat_1(sK0)))) ) | (~spl3_2 | ~spl3_5)),
% 0.22/0.42    inference(resolution,[],[f45,f32])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    r1_xboole_0(sK1,k1_relat_1(sK0)) | ~spl3_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f30])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) ) | ~spl3_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f44])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    spl3_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f23,f52])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ! [X0,X1] : (((k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(nnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    spl3_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f20,f48])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,plain,(
% 0.22/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(rectify,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    spl3_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f21,f44])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    spl3_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f19,f40])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    spl3_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f16,f35])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    v1_relat_1(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    (k1_xboole_0 != k7_relat_1(sK0,sK1) & r1_xboole_0(sK1,k1_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11,f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : (k1_xboole_0 != k7_relat_1(X0,X1) & r1_xboole_0(X1,k1_relat_1(X0))) & v1_relat_1(X0)) => (? [X1] : (k1_xboole_0 != k7_relat_1(sK0,X1) & r1_xboole_0(X1,k1_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ? [X1] : (k1_xboole_0 != k7_relat_1(sK0,X1) & r1_xboole_0(X1,k1_relat_1(sK0))) => (k1_xboole_0 != k7_relat_1(sK0,sK1) & r1_xboole_0(sK1,k1_relat_1(sK0)))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : (k1_xboole_0 != k7_relat_1(X0,X1) & r1_xboole_0(X1,k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,negated_conjecture,(
% 0.22/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.22/0.42    inference(negated_conjecture,[],[f4])).
% 0.22/0.42  fof(f4,conjecture,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    spl3_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f17,f30])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    r1_xboole_0(sK1,k1_relat_1(sK0))),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ~spl3_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f18,f25])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    k1_xboole_0 != k7_relat_1(sK0,sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (25901)------------------------------
% 0.22/0.42  % (25901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (25901)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (25901)Memory used [KB]: 10618
% 0.22/0.42  % (25901)Time elapsed: 0.006 s
% 0.22/0.42  % (25901)------------------------------
% 0.22/0.42  % (25901)------------------------------
% 0.22/0.42  % (25895)Success in time 0.064 s
%------------------------------------------------------------------------------
