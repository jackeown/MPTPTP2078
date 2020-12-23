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
% DateTime   : Thu Dec  3 12:29:35 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 (  99 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f57,f60])).

fof(f60,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f58,f16])).

fof(f16,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f58,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl4_2 ),
    inference(resolution,[],[f46,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f46,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK3))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_2
  <=> r1_tarski(sK2,k2_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f57,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f53,f43])).

fof(f43,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_1
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f53,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f32,f23])).

fof(f23,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f19,f15])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f47,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f36,f45,f42])).

fof(f36,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK3))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f22,f17])).

fof(f17,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n001.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 13:48:30 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.39  % (30001)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.18/0.39  % (30000)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.18/0.39  % (30004)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.18/0.39  % (29999)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.18/0.39  % (30001)Refutation found. Thanks to Tanya!
% 0.18/0.39  % SZS status Theorem for theBenchmark
% 0.18/0.39  % SZS output start Proof for theBenchmark
% 0.18/0.39  fof(f61,plain,(
% 0.18/0.39    $false),
% 0.18/0.39    inference(avatar_sat_refutation,[],[f47,f57,f60])).
% 0.18/0.39  fof(f60,plain,(
% 0.18/0.39    spl4_2),
% 0.18/0.39    inference(avatar_contradiction_clause,[],[f59])).
% 0.18/0.39  fof(f59,plain,(
% 0.18/0.39    $false | spl4_2),
% 0.18/0.39    inference(subsumption_resolution,[],[f58,f16])).
% 0.18/0.39  fof(f16,plain,(
% 0.18/0.39    r1_tarski(sK2,sK3)),
% 0.18/0.39    inference(cnf_transformation,[],[f9])).
% 0.18/0.39  fof(f9,plain,(
% 0.18/0.39    ? [X0,X1,X2,X3] : (~r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.18/0.39    inference(flattening,[],[f8])).
% 0.18/0.39  fof(f8,plain,(
% 0.18/0.39    ? [X0,X1,X2,X3] : (~r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.18/0.39    inference(ennf_transformation,[],[f7])).
% 0.18/0.39  fof(f7,negated_conjecture,(
% 0.18/0.39    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.18/0.39    inference(negated_conjecture,[],[f6])).
% 0.18/0.39  fof(f6,conjecture,(
% 0.18/0.39    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.18/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 0.18/0.39  fof(f58,plain,(
% 0.18/0.39    ~r1_tarski(sK2,sK3) | spl4_2),
% 0.18/0.39    inference(resolution,[],[f46,f20])).
% 0.18/0.39  fof(f20,plain,(
% 0.18/0.39    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.18/0.39    inference(cnf_transformation,[],[f11])).
% 0.18/0.39  fof(f11,plain,(
% 0.18/0.39    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.18/0.39    inference(ennf_transformation,[],[f1])).
% 0.18/0.39  fof(f1,axiom,(
% 0.18/0.39    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.18/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.18/0.39  fof(f46,plain,(
% 0.18/0.39    ~r1_tarski(sK2,k2_xboole_0(sK1,sK3)) | spl4_2),
% 0.18/0.39    inference(avatar_component_clause,[],[f45])).
% 0.18/0.39  fof(f45,plain,(
% 0.18/0.39    spl4_2 <=> r1_tarski(sK2,k2_xboole_0(sK1,sK3))),
% 0.18/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.18/0.39  fof(f57,plain,(
% 0.18/0.39    spl4_1),
% 0.18/0.39    inference(avatar_contradiction_clause,[],[f55])).
% 0.18/0.39  fof(f55,plain,(
% 0.18/0.39    $false | spl4_1),
% 0.18/0.39    inference(resolution,[],[f53,f43])).
% 0.18/0.39  fof(f43,plain,(
% 0.18/0.39    ~r1_tarski(sK0,k2_xboole_0(sK1,sK3)) | spl4_1),
% 0.18/0.39    inference(avatar_component_clause,[],[f42])).
% 0.18/0.39  fof(f42,plain,(
% 0.18/0.39    spl4_1 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK3))),
% 0.18/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.18/0.39  fof(f53,plain,(
% 0.18/0.39    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,X0))) )),
% 0.18/0.39    inference(superposition,[],[f32,f23])).
% 0.18/0.39  fof(f23,plain,(
% 0.18/0.39    sK1 = k2_xboole_0(sK0,sK1)),
% 0.18/0.39    inference(resolution,[],[f19,f15])).
% 0.18/0.39  fof(f15,plain,(
% 0.18/0.39    r1_tarski(sK0,sK1)),
% 0.18/0.39    inference(cnf_transformation,[],[f9])).
% 0.18/0.39  fof(f19,plain,(
% 0.18/0.39    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.18/0.39    inference(cnf_transformation,[],[f10])).
% 0.18/0.39  fof(f10,plain,(
% 0.18/0.39    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.18/0.39    inference(ennf_transformation,[],[f3])).
% 0.18/0.39  fof(f3,axiom,(
% 0.18/0.39    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.18/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.18/0.39  fof(f32,plain,(
% 0.18/0.39    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) )),
% 0.18/0.39    inference(resolution,[],[f21,f18])).
% 0.18/0.39  fof(f18,plain,(
% 0.18/0.39    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.18/0.39    inference(cnf_transformation,[],[f4])).
% 0.18/0.39  fof(f4,axiom,(
% 0.18/0.39    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.18/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.18/0.39  fof(f21,plain,(
% 0.18/0.39    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.18/0.39    inference(cnf_transformation,[],[f12])).
% 0.18/0.39  fof(f12,plain,(
% 0.18/0.39    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.18/0.39    inference(ennf_transformation,[],[f2])).
% 0.18/0.39  fof(f2,axiom,(
% 0.18/0.39    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.18/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.18/0.39  fof(f47,plain,(
% 0.18/0.39    ~spl4_1 | ~spl4_2),
% 0.18/0.39    inference(avatar_split_clause,[],[f36,f45,f42])).
% 0.18/0.39  fof(f36,plain,(
% 0.18/0.39    ~r1_tarski(sK2,k2_xboole_0(sK1,sK3)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK3))),
% 0.18/0.39    inference(resolution,[],[f22,f17])).
% 0.18/0.39  fof(f17,plain,(
% 0.18/0.39    ~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3))),
% 0.18/0.39    inference(cnf_transformation,[],[f9])).
% 0.18/0.39  fof(f22,plain,(
% 0.18/0.39    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.18/0.39    inference(cnf_transformation,[],[f14])).
% 0.18/0.39  fof(f14,plain,(
% 0.18/0.39    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.18/0.39    inference(flattening,[],[f13])).
% 0.18/0.39  fof(f13,plain,(
% 0.18/0.39    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.18/0.39    inference(ennf_transformation,[],[f5])).
% 0.18/0.39  fof(f5,axiom,(
% 0.18/0.39    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.18/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.18/0.39  % SZS output end Proof for theBenchmark
% 0.18/0.39  % (30001)------------------------------
% 0.18/0.39  % (30001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.39  % (30001)Termination reason: Refutation
% 0.18/0.39  
% 0.18/0.39  % (30001)Memory used [KB]: 10618
% 0.18/0.39  % (30001)Time elapsed: 0.029 s
% 0.18/0.39  % (30001)------------------------------
% 0.18/0.39  % (30001)------------------------------
% 0.18/0.39  % (29997)Success in time 0.066 s
%------------------------------------------------------------------------------
