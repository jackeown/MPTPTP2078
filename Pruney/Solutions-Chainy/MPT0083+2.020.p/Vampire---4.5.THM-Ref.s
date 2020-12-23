%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   75 (  99 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f30,f37,f44])).

fof(f44,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f43])).

fof(f43,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f42,f11])).

fof(f11,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f42,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK0)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f40,f11])).

fof(f40,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK0)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f36,f22])).

fof(f22,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ r1_tarski(k3_xboole_0(sK0,sK2),X1) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(k3_xboole_0(sK0,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f37,plain,
    ( spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f33,f27,f35])).

fof(f27,plain,
    ( spl3_3
  <=> r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(k3_xboole_0(sK0,sK2),X1) )
    | spl3_3 ),
    inference(resolution,[],[f13,f29])).

fof(f29,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f30,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f25,f15,f27])).

fof(f15,plain,
    ( spl3_1
  <=> r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f25,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f24,f12])).

fof(f12,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f24,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f17,f12])).

fof(f17,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f23,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f9,f20])).

fof(f9,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f18,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f10,f15])).

fof(f10,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.40  % (18929)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.41  % (18930)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.41  % (18924)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.41  % (18924)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f18,f23,f30,f37,f44])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    ~spl3_2 | ~spl3_4),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f43])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    $false | (~spl3_2 | ~spl3_4)),
% 0.21/0.41    inference(subsumption_resolution,[],[f42,f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    ~r1_tarski(k3_xboole_0(sK0,sK2),sK0) | (~spl3_2 | ~spl3_4)),
% 0.21/0.41    inference(subsumption_resolution,[],[f40,f11])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~r1_tarski(k3_xboole_0(sK0,sK2),sK0) | (~spl3_2 | ~spl3_4)),
% 0.21/0.41    inference(resolution,[],[f36,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    r1_xboole_0(sK0,sK1) | ~spl3_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f20])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    spl3_2 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~r1_tarski(k3_xboole_0(sK0,sK2),X1)) ) | ~spl3_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    spl3_4 <=> ! [X1,X0] : (~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~r1_xboole_0(X1,X0) | ~r1_tarski(k3_xboole_0(sK0,sK2),X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    spl3_4 | spl3_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f33,f27,f35])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    spl3_3 <=> r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~r1_xboole_0(X1,X0) | ~r1_tarski(k3_xboole_0(sK0,sK2),X1)) ) | spl3_3),
% 0.21/0.42    inference(resolution,[],[f13,f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ~r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) | spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f27])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X2,X3) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ~spl3_3 | spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f15,f27])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    spl3_1 <=> r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ~r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) | spl3_1),
% 0.21/0.42    inference(forward_demodulation,[],[f24,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK1,sK2)) | spl3_1),
% 0.21/0.42    inference(forward_demodulation,[],[f17,f12])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f15])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f9,f20])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f10,f15])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (18924)------------------------------
% 0.21/0.42  % (18924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (18924)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (18924)Memory used [KB]: 10618
% 0.21/0.42  % (18924)Time elapsed: 0.005 s
% 0.21/0.42  % (18924)------------------------------
% 0.21/0.42  % (18924)------------------------------
% 0.21/0.42  % (18922)Success in time 0.066 s
%------------------------------------------------------------------------------
