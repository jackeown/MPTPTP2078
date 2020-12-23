%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  91 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 225 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f42,f54,f73,f79,f88,f118])).

fof(f118,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f117,f76,f51,f35])).

fof(f35,plain,
    ( spl3_3
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51,plain,
    ( spl3_5
  <=> k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f76,plain,
    ( spl3_9
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f117,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f91,f53])).

fof(f53,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f91,plain,
    ( ! [X0] : r2_hidden(sK1,k2_xboole_0(X0,k2_relat_1(sK2)))
    | ~ spl3_9 ),
    inference(superposition,[],[f83,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f83,plain,
    ( ! [X2] : r2_hidden(sK1,k2_xboole_0(k2_relat_1(sK2),X2))
    | ~ spl3_9 ),
    inference(resolution,[],[f47,f78])).

fof(f78,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k2_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f88,plain,
    ( spl3_4
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f85,f70,f51,f39])).

fof(f39,plain,
    ( spl3_4
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f70,plain,
    ( spl3_8
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f85,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(superposition,[],[f82,f53])).

fof(f82,plain,
    ( ! [X1] : r2_hidden(sK0,k2_xboole_0(k1_relat_1(sK2),X1))
    | ~ spl3_8 ),
    inference(resolution,[],[f47,f72])).

fof(f72,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f79,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f74,f25,f30,f76])).

fof(f30,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f25,plain,
    ( spl3_1
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f74,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f23,f27])).

fof(f27,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f73,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f68,f25,f30,f70])).

fof(f68,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f22,f27])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f49,f30,f51])).

fof(f49,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f18,f32])).

fof(f32,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f42,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f15,f39,f35])).

fof(f15,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f25])).

fof(f17,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:31:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (23481)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (23496)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.49  % (23481)Refutation not found, incomplete strategy% (23481)------------------------------
% 0.20/0.49  % (23481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23481)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23481)Memory used [KB]: 10618
% 0.20/0.49  % (23481)Time elapsed: 0.056 s
% 0.20/0.49  % (23481)------------------------------
% 0.20/0.49  % (23481)------------------------------
% 0.20/0.49  % (23502)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (23490)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (23496)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f28,f33,f42,f54,f73,f79,f88,f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    spl3_3 | ~spl3_5 | ~spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f117,f76,f51,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    spl3_3 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    spl3_5 <=> k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl3_9 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    r2_hidden(sK1,k3_relat_1(sK2)) | (~spl3_5 | ~spl3_9)),
% 0.20/0.50    inference(superposition,[],[f91,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f51])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK1,k2_xboole_0(X0,k2_relat_1(sK2)))) ) | ~spl3_9),
% 0.20/0.50    inference(superposition,[],[f83,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X2] : (r2_hidden(sK1,k2_xboole_0(k2_relat_1(sK2),X2))) ) | ~spl3_9),
% 0.20/0.50    inference(resolution,[],[f47,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl3_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f76])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(resolution,[],[f21,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.50    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    spl3_4 | ~spl3_5 | ~spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f85,f70,f51,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    spl3_4 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    spl3_8 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    r2_hidden(sK0,k3_relat_1(sK2)) | (~spl3_5 | ~spl3_8)),
% 0.20/0.50    inference(superposition,[],[f82,f53])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X1] : (r2_hidden(sK0,k2_xboole_0(k1_relat_1(sK2),X1))) ) | ~spl3_8),
% 0.20/0.50    inference(resolution,[],[f47,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl3_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f70])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl3_9 | ~spl3_2 | ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f74,f25,f30,f76])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    spl3_2 <=> v1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    spl3_1 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | r2_hidden(sK1,k2_relat_1(sK2)) | ~spl3_1),
% 0.20/0.50    inference(resolution,[],[f23,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f25])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    spl3_8 | ~spl3_2 | ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f68,f25,f30,f70])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~spl3_1),
% 0.20/0.50    inference(resolution,[],[f22,f27])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    spl3_5 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f49,f30,f51])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f18,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    v1_relat_1(sK2) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f30])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ~spl3_3 | ~spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f15,f39,f35])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f6])).
% 0.20/0.50  fof(f6,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f16,f30])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f17,f25])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (23496)------------------------------
% 0.20/0.50  % (23496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23496)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (23496)Memory used [KB]: 10746
% 0.20/0.50  % (23496)Time elapsed: 0.051 s
% 0.20/0.50  % (23496)------------------------------
% 0.20/0.50  % (23496)------------------------------
% 0.20/0.50  % (23490)Refutation not found, incomplete strategy% (23490)------------------------------
% 0.20/0.50  % (23490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23490)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (23490)Memory used [KB]: 10618
% 0.20/0.50  % (23490)Time elapsed: 0.071 s
% 0.20/0.50  % (23490)------------------------------
% 0.20/0.50  % (23490)------------------------------
% 0.20/0.50  % (23476)Success in time 0.143 s
%------------------------------------------------------------------------------
