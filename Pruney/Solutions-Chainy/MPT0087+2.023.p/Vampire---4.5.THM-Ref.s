%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 ( 101 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23906)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f34,f42,f82,f89])).

fof(f89,plain,
    ( ~ spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f20,f87])).

fof(f87,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(superposition,[],[f81,f41])).

fof(f41,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_6
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f81,plain,
    ( ! [X0] : ~ r1_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_10
  <=> ! [X0] : ~ r1_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f20,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f82,plain,
    ( spl3_10
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f44,f32,f23,f80])).

fof(f23,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f32,plain,
    ( spl3_4
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f44,plain,
    ( ! [X0] : ~ r1_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2)))
    | spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f25,f33])).

fof(f33,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f32])).

fof(f25,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f42,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f13,f40])).

% (23905)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f34,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f26,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f11,f23])).

fof(f11,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f21,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f10,f18])).

fof(f10,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:27:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (23908)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (23908)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  % (23906)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f21,f26,f34,f42,f82,f89])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_6 | ~spl3_10),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_6 | ~spl3_10)),
% 0.21/0.46    inference(subsumption_resolution,[],[f20,f87])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ~r1_xboole_0(sK0,sK1) | (~spl3_6 | ~spl3_10)),
% 0.21/0.46    inference(superposition,[],[f81,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    spl3_6 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2)))) ) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f80])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    spl3_10 <=> ! [X0] : ~r1_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    spl3_10 | spl3_2 | ~spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f44,f32,f23,f80])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    spl3_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    spl3_4 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2)))) ) | (spl3_2 | ~spl3_4)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f25,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) ) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f32])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f23])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f13,f40])).
% 0.21/0.46  % (23905)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f32])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f11,f23])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.46    inference(negated_conjecture,[],[f4])).
% 0.21/0.46  fof(f4,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f10,f18])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    r1_xboole_0(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (23908)------------------------------
% 0.21/0.46  % (23908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (23908)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (23908)Memory used [KB]: 6140
% 0.21/0.46  % (23908)Time elapsed: 0.044 s
% 0.21/0.46  % (23908)------------------------------
% 0.21/0.46  % (23908)------------------------------
% 0.21/0.47  % (23902)Success in time 0.106 s
%------------------------------------------------------------------------------
