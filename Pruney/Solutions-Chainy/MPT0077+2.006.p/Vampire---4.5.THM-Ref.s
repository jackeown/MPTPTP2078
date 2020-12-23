%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 117 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  162 ( 323 expanded)
%              Number of equality atoms :   18 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f416,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f100,f132,f415])).

fof(f415,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f413,f42])).

fof(f42,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_4
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f413,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f406,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f406,plain,
    ( k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(superposition,[],[f325,f134])).

fof(f134,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f37,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f325,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1))
        | r1_xboole_0(sK0,k2_xboole_0(sK1,X1)) )
    | ~ spl4_2 ),
    inference(superposition,[],[f21,f156])).

fof(f156,plain,
    ( ! [X0] : k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
    | ~ spl4_2 ),
    inference(superposition,[],[f23,f133])).

fof(f133,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f32,f22])).

fof(f32,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f132,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f124,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f19,f18])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f124,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f103,f68])).

fof(f68,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_1 ),
    inference(superposition,[],[f21,f64])).

fof(f64,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f61,f28])).

fof(f28,plain,
    ( sP3(sK2,sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl4_1
  <=> sP3(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f61,plain,(
    ! [X4,X5,X3] :
      ( ~ sP3(X5,X4,X3)
      | k1_xboole_0 = k3_xboole_0(X3,k2_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f22,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ sP3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,k2_xboole_0(sK1,X0))
        | ~ r1_tarski(sK0,X1) )
    | spl4_2 ),
    inference(resolution,[],[f101,f19])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(sK0,X1) )
    | spl4_2 ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f31,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f100,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f98,f48])).

fof(f98,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f92,f28])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ sP3(sK2,X1,X0)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f70,f50])).

fof(f50,plain,(
    ! [X4,X2,X3] :
      ( r1_xboole_0(X4,k2_xboole_0(X3,X2))
      | ~ sP3(X3,X2,X4) ) ),
    inference(superposition,[],[f14,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,k2_xboole_0(sK2,X0))
        | ~ r1_tarski(sK0,X1) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f65,f19])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(sK0,X1) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f24,f45])).

fof(f45,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f44,f32])).

fof(f44,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f13,f28])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X2,X1,X0)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f15,f40,f26])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f17,f35,f26])).

fof(f17,plain,
    ( r1_xboole_0(sK0,sK2)
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f16,f30,f26])).

fof(f16,plain,
    ( r1_xboole_0(sK0,sK1)
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (15990)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.41  % (15979)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.42  % (15979)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f416,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f33,f38,f43,f100,f132,f415])).
% 0.21/0.42  fof(f415,plain,(
% 0.21/0.42    ~spl4_2 | ~spl4_3 | spl4_4),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f414])).
% 0.21/0.42  fof(f414,plain,(
% 0.21/0.42    $false | (~spl4_2 | ~spl4_3 | spl4_4)),
% 0.21/0.42    inference(subsumption_resolution,[],[f413,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl4_4 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f413,plain,(
% 0.21/0.42    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl4_2 | ~spl4_3)),
% 0.21/0.42    inference(subsumption_resolution,[],[f406,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.42    inference(rectify,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.42  fof(f406,plain,(
% 0.21/0.42    k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0) | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl4_2 | ~spl4_3)),
% 0.21/0.42    inference(superposition,[],[f325,f134])).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl4_3),
% 0.21/0.42    inference(resolution,[],[f37,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK2) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl4_3 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f325,plain,(
% 0.21/0.42    ( ! [X1] : (k1_xboole_0 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1)) | r1_xboole_0(sK0,k2_xboole_0(sK1,X1))) ) | ~spl4_2),
% 0.21/0.42    inference(superposition,[],[f21,f156])).
% 0.21/0.42  fof(f156,plain,(
% 0.21/0.42    ( ! [X0] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ) | ~spl4_2),
% 0.21/0.42    inference(superposition,[],[f23,f133])).
% 0.21/0.42  fof(f133,plain,(
% 0.21/0.42    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_2),
% 0.21/0.42    inference(resolution,[],[f32,f22])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl4_2 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    ~spl4_1 | spl4_2),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f131])).
% 0.21/0.42  fof(f131,plain,(
% 0.21/0.42    $false | (~spl4_1 | spl4_2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f124,f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.42    inference(superposition,[],[f19,f18])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    ~r1_tarski(sK0,sK0) | (~spl4_1 | spl4_2)),
% 0.21/0.42    inference(resolution,[],[f103,f68])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl4_1),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f67])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl4_1),
% 0.21/0.42    inference(superposition,[],[f21,f64])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl4_1),
% 0.21/0.42    inference(resolution,[],[f61,f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    sP3(sK2,sK1,sK0) | ~spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    spl4_1 <=> sP3(sK2,sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X4,X5,X3] : (~sP3(X5,X4,X3) | k1_xboole_0 = k3_xboole_0(X3,k2_xboole_0(X4,X5))) )),
% 0.21/0.42    inference(resolution,[],[f22,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~sP3(X2,X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X1,k2_xboole_0(sK1,X0)) | ~r1_tarski(sK0,X1)) ) | spl4_2),
% 0.21/0.42    inference(resolution,[],[f101,f19])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(sK1,X0) | ~r1_xboole_0(X1,X0) | ~r1_tarski(sK0,X1)) ) | spl4_2),
% 0.21/0.42    inference(resolution,[],[f31,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X2,X3) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,sK1) | spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f30])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    ~spl4_1 | ~spl4_2),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f99])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    $false | (~spl4_1 | ~spl4_2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f98,f48])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    ~r1_tarski(sK0,sK0) | (~spl4_1 | ~spl4_2)),
% 0.21/0.42    inference(resolution,[],[f92,f28])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~sP3(sK2,X1,X0) | ~r1_tarski(sK0,X0)) ) | (~spl4_1 | ~spl4_2)),
% 0.21/0.42    inference(resolution,[],[f70,f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ( ! [X4,X2,X3] : (r1_xboole_0(X4,k2_xboole_0(X3,X2)) | ~sP3(X3,X2,X4)) )),
% 0.21/0.42    inference(superposition,[],[f14,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X1,k2_xboole_0(sK2,X0)) | ~r1_tarski(sK0,X1)) ) | (~spl4_1 | ~spl4_2)),
% 0.21/0.42    inference(resolution,[],[f65,f19])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(sK2,X0) | ~r1_xboole_0(X1,X0) | ~r1_tarski(sK0,X1)) ) | (~spl4_1 | ~spl4_2)),
% 0.21/0.42    inference(resolution,[],[f24,f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,sK2) | (~spl4_1 | ~spl4_2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f44,f32])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~spl4_1),
% 0.21/0.42    inference(resolution,[],[f13,f28])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~sP3(X2,X1,X0) | ~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl4_1 | ~spl4_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f40,f26])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | sP3(sK2,sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl4_1 | spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f35,f26])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK2) | sP3(sK2,sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl4_1 | spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f30,f26])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1) | sP3(sK2,sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (15979)------------------------------
% 0.21/0.42  % (15979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (15979)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (15979)Memory used [KB]: 10746
% 0.21/0.42  % (15987)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.42  % (15979)Time elapsed: 0.014 s
% 0.21/0.42  % (15979)------------------------------
% 0.21/0.42  % (15979)------------------------------
% 0.21/0.43  % (15978)Success in time 0.07 s
%------------------------------------------------------------------------------
