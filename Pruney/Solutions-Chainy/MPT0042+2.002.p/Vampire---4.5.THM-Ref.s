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
% DateTime   : Thu Dec  3 12:29:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  66 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   94 ( 138 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f61,f70,f106,f174])).

fof(f174,plain,
    ( ~ spl4_2
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl4_2
    | spl4_13 ),
    inference(subsumption_resolution,[],[f171,f30])).

fof(f30,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f171,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl4_13 ),
    inference(resolution,[],[f105,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f105,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK0,sK2))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_13
  <=> r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f106,plain,
    ( ~ spl4_13
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f100,f68,f59,f103])).

fof(f59,plain,
    ( spl4_6
  <=> ! [X0] : ~ r1_tarski(k4_xboole_0(sK0,sK3),k3_xboole_0(X0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f68,plain,
    ( spl4_7
  <=> ! [X12] : k4_xboole_0(sK0,X12) = k3_xboole_0(k4_xboole_0(sK0,X12),k4_xboole_0(sK1,X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f100,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK0,sK2))
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(superposition,[],[f60,f69])).

fof(f69,plain,
    ( ! [X12] : k4_xboole_0(sK0,X12) = k3_xboole_0(k4_xboole_0(sK0,X12),k4_xboole_0(sK1,X12))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f60,plain,
    ( ! [X0] : ~ r1_tarski(k4_xboole_0(sK0,sK3),k3_xboole_0(X0,k4_xboole_0(sK1,sK2)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f70,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f65,f33,f68])).

fof(f33,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f65,plain,
    ( ! [X12] : k4_xboole_0(sK0,X12) = k3_xboole_0(k4_xboole_0(sK0,X12),k4_xboole_0(sK1,X12))
    | ~ spl4_3 ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X2) = k3_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f19,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f61,plain,
    ( spl4_6
    | spl4_1 ),
    inference(avatar_split_clause,[],[f55,f23,f59])).

fof(f23,plain,
    ( spl4_1
  <=> r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f55,plain,
    ( ! [X0] : ~ r1_tarski(k4_xboole_0(sK0,sK3),k3_xboole_0(X0,k4_xboole_0(sK1,sK2)))
    | spl4_1 ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r1_tarski(X2,k3_xboole_0(X1,X0)) ) ),
    inference(superposition,[],[f21,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f36,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).

fof(f31,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f26,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f23])).

fof(f16,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:20:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.39  % (16553)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.41  % (16548)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.42  % (16548)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f179,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f26,f31,f36,f61,f70,f106,f174])).
% 0.21/0.42  fof(f174,plain,(
% 0.21/0.42    ~spl4_2 | spl4_13),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f173])).
% 0.21/0.42  fof(f173,plain,(
% 0.21/0.42    $false | (~spl4_2 | spl4_13)),
% 0.21/0.42    inference(subsumption_resolution,[],[f171,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl4_2 <=> r1_tarski(sK2,sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f171,plain,(
% 0.21/0.42    ~r1_tarski(sK2,sK3) | spl4_13),
% 0.21/0.42    inference(resolution,[],[f105,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    ~r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK0,sK2)) | spl4_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f103])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl4_13 <=> r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK0,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    ~spl4_13 | ~spl4_6 | ~spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f100,f68,f59,f103])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl4_6 <=> ! [X0] : ~r1_tarski(k4_xboole_0(sK0,sK3),k3_xboole_0(X0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl4_7 <=> ! [X12] : k4_xboole_0(sK0,X12) = k3_xboole_0(k4_xboole_0(sK0,X12),k4_xboole_0(sK1,X12))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    ~r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK0,sK2)) | (~spl4_6 | ~spl4_7)),
% 0.21/0.42    inference(superposition,[],[f60,f69])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ( ! [X12] : (k4_xboole_0(sK0,X12) = k3_xboole_0(k4_xboole_0(sK0,X12),k4_xboole_0(sK1,X12))) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f68])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK0,sK3),k3_xboole_0(X0,k4_xboole_0(sK1,sK2)))) ) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f59])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl4_7 | ~spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f65,f33,f68])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X12] : (k4_xboole_0(sK0,X12) = k3_xboole_0(k4_xboole_0(sK0,X12),k4_xboole_0(sK1,X12))) ) | ~spl4_3),
% 0.21/0.42    inference(resolution,[],[f51,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f33])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X2) = k3_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.21/0.42    inference(resolution,[],[f19,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl4_6 | spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f55,f23,f59])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    spl4_1 <=> r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK0,sK3),k3_xboole_0(X0,k4_xboole_0(sK1,sK2)))) ) | spl4_1),
% 0.21/0.42    inference(resolution,[],[f49,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ~r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2)) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f23])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r1_tarski(X2,k3_xboole_0(X1,X0))) )),
% 0.21/0.42    inference(superposition,[],[f21,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f33])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    r1_tarski(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f28])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    r1_tarski(sK2,sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ~spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f23])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ~r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2))),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (16548)------------------------------
% 0.21/0.42  % (16548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (16548)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (16548)Memory used [KB]: 10618
% 0.21/0.42  % (16548)Time elapsed: 0.009 s
% 0.21/0.42  % (16548)------------------------------
% 0.21/0.42  % (16548)------------------------------
% 0.21/0.42  % (16546)Success in time 0.065 s
%------------------------------------------------------------------------------
