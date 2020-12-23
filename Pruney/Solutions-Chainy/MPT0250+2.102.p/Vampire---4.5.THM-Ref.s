%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  39 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 (  82 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f42,f45])).

fof(f45,plain,
    ( spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f43,f39,f27])).

fof(f27,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f39,plain,
    ( spl2_3
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f43,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f41,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f41,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f42,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f37,f32,f39])).

fof(f32,plain,
    ( spl2_2
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f37,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f36,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f36,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(sK0),sK1))
        | r1_tarski(X0,sK1) )
    | ~ spl2_2 ),
    inference(resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f34,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f30,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f27])).

fof(f17,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (30948)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.41  % (30948)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f30,f35,f42,f45])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    spl2_1 | ~spl2_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f43,f39,f27])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    spl2_3 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    r2_hidden(sK0,sK1) | ~spl2_3),
% 0.21/0.41    inference(resolution,[],[f41,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.41    inference(nnf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    r1_tarski(k1_tarski(sK0),sK1) | ~spl2_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f39])).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    spl2_3 | ~spl2_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f37,f32,f39])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    spl2_2 <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    r1_tarski(k1_tarski(sK0),sK1) | ~spl2_2),
% 0.21/0.41    inference(resolution,[],[f36,f19])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(k1_tarski(sK0),sK1)) | r1_tarski(X0,sK1)) ) | ~spl2_2),
% 0.21/0.41    inference(resolution,[],[f34,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(flattening,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) | ~spl2_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f32])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    spl2_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f16,f32])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.21/0.41    inference(negated_conjecture,[],[f8])).
% 0.21/0.41  fof(f8,conjecture,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ~spl2_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f17,f27])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ~r2_hidden(sK0,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (30948)------------------------------
% 0.21/0.41  % (30948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (30948)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (30948)Memory used [KB]: 10618
% 0.21/0.41  % (30948)Time elapsed: 0.004 s
% 0.21/0.41  % (30948)------------------------------
% 0.21/0.41  % (30948)------------------------------
% 0.21/0.41  % (30935)Success in time 0.058 s
%------------------------------------------------------------------------------
