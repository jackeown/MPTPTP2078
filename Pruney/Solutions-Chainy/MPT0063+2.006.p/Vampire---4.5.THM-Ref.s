%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  51 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 139 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f42,f68])).

fof(f68,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f51,f41])).

fof(f41,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f24,f29,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X2)
      | r2_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l58_xboole_1)).

fof(f29,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_2
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f24,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f37,f32,f39])).

fof(f32,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f37,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f34,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f34,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f32])).

fof(f13,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r2_xboole_0(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r2_xboole_0(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f22])).

fof(f15,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:41:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (11139)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.45  % (11139)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f25,f30,f35,f42,f68])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    spl3_1 | ~spl3_2 | ~spl3_4),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    $false | (spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.21/0.45    inference(subsumption_resolution,[],[f51,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    spl3_4 <=> r1_tarski(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ~r1_tarski(sK0,sK1) | (spl3_1 | ~spl3_2)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f24,f29,f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X2) | r2_xboole_0(X0,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l58_xboole_1)).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    r2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    spl3_2 <=> r2_xboole_0(sK1,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ~r2_xboole_0(sK0,sK2) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    spl3_1 <=> r2_xboole_0(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    spl3_4 | ~spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f37,f32,f39])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    spl3_3 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f34,f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.45    inference(flattening,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    r2_xboole_0(sK0,sK1) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f32])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f13,f32])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    r2_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r2_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r2_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f6,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f5])).
% 0.21/0.45  fof(f5,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.45    inference(negated_conjecture,[],[f3])).
% 0.21/0.45  fof(f3,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f14,f27])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    r2_xboole_0(sK1,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ~spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f15,f22])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ~r2_xboole_0(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (11139)------------------------------
% 0.21/0.45  % (11139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (11139)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (11139)Memory used [KB]: 10618
% 0.21/0.45  % (11139)Time elapsed: 0.031 s
% 0.21/0.45  % (11139)------------------------------
% 0.21/0.45  % (11139)------------------------------
% 0.21/0.45  % (11122)Success in time 0.084 s
%------------------------------------------------------------------------------
