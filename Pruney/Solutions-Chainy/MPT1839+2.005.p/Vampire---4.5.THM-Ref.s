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
% DateTime   : Thu Dec  3 13:20:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  72 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   97 ( 174 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f51,f59,f69])).

fof(f69,plain,
    ( spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f67,f56,f32])).

fof(f32,plain,
    ( spl2_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f56,plain,
    ( spl2_6
  <=> sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f67,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_6 ),
    inference(superposition,[],[f41,f58])).

fof(f58,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f20,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f59,plain,
    ( spl2_6
    | spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f52,f49,f37,f56])).

fof(f37,plain,
    ( spl2_4
  <=> v1_xboole_0(k1_setfam_1(k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f49,plain,
    ( spl2_5
  <=> ! [X0] :
        ( v1_xboole_0(k1_setfam_1(k2_tarski(sK0,X0)))
        | sK0 = k1_setfam_1(k2_tarski(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f52,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | spl2_4
    | ~ spl2_5 ),
    inference(resolution,[],[f50,f39])).

fof(f39,plain,
    ( ~ v1_xboole_0(k1_setfam_1(k2_tarski(sK0,sK1)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f50,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_setfam_1(k2_tarski(sK0,X0)))
        | sK0 = k1_setfam_1(k2_tarski(sK0,X0)) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f51,plain,
    ( spl2_5
    | spl2_2
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f47,f22,f27,f49])).

fof(f27,plain,
    ( spl2_2
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f22,plain,
    ( spl2_1
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | v1_xboole_0(k1_setfam_1(k2_tarski(sK0,X0)))
        | sK0 = k1_setfam_1(k2_tarski(sK0,X0)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f43,f24])).

fof(f24,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(k1_setfam_1(k2_tarski(X0,X1)))
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(resolution,[],[f15,f20])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f40,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    ~ v1_xboole_0(k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f11,f18])).

fof(f11,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(f35,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f12,f32])).

fof(f12,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f14,f22])).

fof(f14,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (17885)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.47  % (17890)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.47  % (17885)Refutation not found, incomplete strategy% (17885)------------------------------
% 0.21/0.47  % (17885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17885)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (17885)Memory used [KB]: 10618
% 0.21/0.47  % (17885)Time elapsed: 0.058 s
% 0.21/0.47  % (17885)------------------------------
% 0.21/0.47  % (17885)------------------------------
% 0.21/0.48  % (17890)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f51,f59,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl2_3 | ~spl2_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f67,f56,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl2_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl2_6 <=> sK0 = k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | ~spl2_6),
% 0.21/0.48    inference(superposition,[],[f41,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) | ~spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 0.21/0.48    inference(superposition,[],[f20,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f16,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl2_6 | spl2_4 | ~spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f52,f49,f37,f56])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl2_4 <=> v1_xboole_0(k1_setfam_1(k2_tarski(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl2_5 <=> ! [X0] : (v1_xboole_0(k1_setfam_1(k2_tarski(sK0,X0))) | sK0 = k1_setfam_1(k2_tarski(sK0,X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) | (spl2_4 | ~spl2_5)),
% 0.21/0.48    inference(resolution,[],[f50,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_setfam_1(k2_tarski(sK0,sK1))) | spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f37])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(k1_setfam_1(k2_tarski(sK0,X0))) | sK0 = k1_setfam_1(k2_tarski(sK0,X0))) ) | ~spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl2_5 | spl2_2 | ~spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f22,f27,f49])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    spl2_2 <=> v1_xboole_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    spl2_1 <=> v1_zfmisc_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(sK0) | v1_xboole_0(k1_setfam_1(k2_tarski(sK0,X0))) | sK0 = k1_setfam_1(k2_tarski(sK0,X0))) ) | ~spl2_1),
% 0.21/0.48    inference(resolution,[],[f43,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v1_zfmisc_1(sK0) | ~spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f22])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X0) | v1_xboole_0(k1_setfam_1(k2_tarski(X0,X1))) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.21/0.48    inference(resolution,[],[f15,f20])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X0) | X0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ~spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f37])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_setfam_1(k2_tarski(sK0,sK1)))),
% 0.21/0.48    inference(definition_unfolding,[],[f11,f18])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f12,f32])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f27])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f22])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    v1_zfmisc_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17890)------------------------------
% 0.21/0.48  % (17890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17890)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17890)Memory used [KB]: 10746
% 0.21/0.48  % (17890)Time elapsed: 0.073 s
% 0.21/0.48  % (17890)------------------------------
% 0.21/0.48  % (17890)------------------------------
% 0.21/0.48  % (17872)Success in time 0.123 s
%------------------------------------------------------------------------------
