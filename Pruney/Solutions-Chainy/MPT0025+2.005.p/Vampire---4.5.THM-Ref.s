%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  51 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   81 ( 119 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f27,f31,f36,f43,f46])).

fof(f46,plain,
    ( ~ spl3_3
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f44])).

fof(f44,plain,
    ( $false
    | ~ spl3_3
    | spl3_6 ),
    inference(resolution,[],[f42,f26])).

fof(f26,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f42,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_6
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f43,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f37,f34,f20,f40])).

fof(f20,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f34,plain,
    ( spl3_5
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f37,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f35,f22])).

fof(f22,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f35,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f34])).

fof(f36,plain,
    ( spl3_5
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f32,f29,f15,f34])).

fof(f15,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f29,plain,
    ( spl3_4
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f32,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK0,X0) )
    | spl3_1
    | ~ spl3_4 ),
    inference(resolution,[],[f30,f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f30,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f31,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f27,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f23,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f10,f20])).

fof(f10,plain,(
    r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k3_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f18,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f11,f15])).

fof(f11,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:01:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.45  % (19671)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.20/0.45  % (19669)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.45  % (19671)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f18,f23,f27,f31,f36,f43,f46])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ~spl3_3 | spl3_6),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    $false | (~spl3_3 | spl3_6)),
% 0.20/0.45    inference(resolution,[],[f42,f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    spl3_3 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | spl3_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    spl3_6 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ~spl3_6 | ~spl3_2 | ~spl3_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f37,f34,f20,f40])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    spl3_2 <=> r1_tarski(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    spl3_5 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK0,X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | (~spl3_2 | ~spl3_5)),
% 0.20/0.45    inference(resolution,[],[f35,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    r1_tarski(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f20])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,sK1)) ) | ~spl3_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f34])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    spl3_5 | spl3_1 | ~spl3_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f32,f29,f15,f34])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    spl3_4 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK0,X0)) ) | (spl3_1 | ~spl3_4)),
% 0.20/0.45    inference(resolution,[],[f30,f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f15])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f29])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    spl3_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f13,f29])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f6])).
% 0.20/0.45  fof(f6,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f12,f25])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f10,f20])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    r1_tarski(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k3_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k3_xboole_0(sK1,sK2)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f5,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.45    inference(negated_conjecture,[],[f3])).
% 0.20/0.45  fof(f3,conjecture,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ~spl3_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f11,f15])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ~r1_tarski(sK0,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (19671)------------------------------
% 0.20/0.45  % (19671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (19671)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (19661)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.46  % (19663)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (19670)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.46  % (19667)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.46  % (19662)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.46  % (19659)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.47  % (19671)Memory used [KB]: 5373
% 0.20/0.47  % (19671)Time elapsed: 0.049 s
% 0.20/0.47  % (19671)------------------------------
% 0.20/0.47  % (19671)------------------------------
% 0.20/0.47  % (19654)Success in time 0.117 s
%------------------------------------------------------------------------------
