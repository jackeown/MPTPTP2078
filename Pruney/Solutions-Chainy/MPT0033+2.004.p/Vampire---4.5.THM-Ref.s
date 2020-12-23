%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  67 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 125 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f50,f55,f83,f100,f148])).

fof(f148,plain,
    ( ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f142,f16])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f142,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK0)
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(superposition,[],[f98,f82])).

fof(f82,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_8
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f98,plain,
    ( ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_10
  <=> ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f100,plain,
    ( spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f90,f53,f97])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f90,plain,
    ( ! [X1] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f54,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f54,plain,
    ( ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f83,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f73,f28,f80])).

fof(f28,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f73,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f35,f30])).

fof(f30,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(superposition,[],[f18,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f55,plain,
    ( spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f51,f47,f53])).

fof(f47,plain,
    ( spl3_4
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,
    ( ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))
    | spl3_4 ),
    inference(resolution,[],[f49,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f49,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f50,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f45,f23,f47])).

fof(f23,plain,
    ( spl3_1
  <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f45,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f16,f17])).

fof(f41,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl3_1 ),
    inference(resolution,[],[f21,f25])).

fof(f25,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f31,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f26,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f23])).

fof(f15,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (14262)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.42  % (14262)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f149,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f26,f31,f50,f55,f83,f100,f148])).
% 0.20/0.42  fof(f148,plain,(
% 0.20/0.42    ~spl3_8 | ~spl3_10),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f147])).
% 0.20/0.42  fof(f147,plain,(
% 0.20/0.42    $false | (~spl3_8 | ~spl3_10)),
% 0.20/0.42    inference(subsumption_resolution,[],[f142,f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.42  fof(f142,plain,(
% 0.20/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK0) | (~spl3_8 | ~spl3_10)),
% 0.20/0.42    inference(superposition,[],[f98,f82])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f80])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    spl3_8 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.42  fof(f98,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1))) ) | ~spl3_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f97])).
% 0.20/0.42  fof(f97,plain,(
% 0.20/0.42    spl3_10 <=> ! [X0] : ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.42  fof(f100,plain,(
% 0.20/0.42    spl3_10 | ~spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f90,f53,f97])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl3_5 <=> ! [X0] : ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.42  fof(f90,plain,(
% 0.20/0.42    ( ! [X1] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK1))) ) | ~spl3_5),
% 0.20/0.42    inference(superposition,[],[f54,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))) ) | ~spl3_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f53])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    spl3_8 | ~spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f73,f28,f80])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_2),
% 0.20/0.42    inference(resolution,[],[f35,f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f28])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.42    inference(superposition,[],[f18,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl3_5 | spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f51,f47,f53])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    spl3_4 <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))) ) | spl3_4),
% 0.20/0.42    inference(resolution,[],[f49,f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f47])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    ~spl3_4 | spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f45,f23,f47])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    spl3_1 <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | spl3_1),
% 0.20/0.42    inference(subsumption_resolution,[],[f41,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.20/0.42    inference(superposition,[],[f16,f17])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK2) | ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | spl3_1),
% 0.20/0.42    inference(resolution,[],[f21,f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) | spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f23])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f14,f28])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) & r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 0.20/0.42    inference(negated_conjecture,[],[f7])).
% 0.20/0.42  fof(f7,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ~spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f23])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (14262)------------------------------
% 0.20/0.42  % (14262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (14262)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (14262)Memory used [KB]: 10618
% 0.20/0.42  % (14262)Time elapsed: 0.007 s
% 0.20/0.42  % (14262)------------------------------
% 0.20/0.42  % (14262)------------------------------
% 0.20/0.42  % (14269)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (14260)Success in time 0.07 s
%------------------------------------------------------------------------------
