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
% DateTime   : Thu Dec  3 13:08:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 103 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  171 ( 279 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f45,f70,f282,f303])).

fof(f303,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f301,f37])).

fof(f37,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_2
  <=> v1_finset_1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f301,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f298,f34])).

fof(f34,plain,
    ( v1_finset_1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_1
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f298,plain,
    ( ~ v1_finset_1(sK0)
    | v1_finset_1(k3_tarski(sK0))
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f297,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_finset_1(sK2(X0))
      | ~ v1_finset_1(X0)
      | v1_finset_1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
     => v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_finset_1)).

fof(f297,plain,
    ( v1_finset_1(sK2(sK0))
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f295,f291])).

fof(f291,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f128,f37])).

fof(f128,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | v1_finset_1(k3_tarski(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f24,f34])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | r2_hidden(sK2(X0),X0)
      | v1_finset_1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f295,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | v1_finset_1(X1) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f18,f37])).

fof(f18,plain,(
    ! [X1] :
      ( v1_finset_1(k3_tarski(sK0))
      | ~ r2_hidden(X1,sK0)
      | v1_finset_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) )
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( ! [X1] :
              ( r2_hidden(X1,X0)
             => v1_finset_1(X1) )
          & v1_finset_1(X0) )
      <=> v1_finset_1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
    <=> v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_finset_1)).

fof(f282,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f280,f44])).

fof(f44,plain,
    ( ~ v1_finset_1(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_3
  <=> v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f280,plain,
    ( v1_finset_1(sK1)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f279,f38])).

fof(f38,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f279,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK1)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f271,f26])).

% (30266)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_finset_1(X1)
      | v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

fof(f271,plain,
    ( r1_tarski(sK1,k3_tarski(sK0))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f178,f74])).

fof(f74,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f71,f34])).

fof(f71,plain,
    ( ~ v1_finset_1(sK0)
    | r2_hidden(sK1,sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f19,f38])).

fof(f19,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0)
    | r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f178,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | r1_tarski(X2,k3_tarski(X3)) ) ),
    inference(resolution,[],[f30,f83])).

fof(f83,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f70,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f68,f33])).

fof(f33,plain,
    ( ~ v1_finset_1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f68,plain,
    ( v1_finset_1(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f48,f46])).

fof(f46,plain,
    ( v1_finset_1(k1_zfmisc_1(k3_tarski(sK0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f23,f38])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | v1_finset_1(k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_finset_1)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k1_zfmisc_1(k3_tarski(X0)))
      | v1_finset_1(X0) ) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f45,plain,
    ( ~ spl4_3
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f40,f36,f32,f42])).

fof(f40,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_finset_1(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f20,f38])).

fof(f20,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0)
    | ~ v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f21,f36,f32])).

fof(f21,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (30267)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.45  % (30275)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % (30268)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (30277)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.47  % (30277)Refutation not found, incomplete strategy% (30277)------------------------------
% 0.21/0.47  % (30277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30269)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (30277)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (30277)Memory used [KB]: 5373
% 0.21/0.47  % (30277)Time elapsed: 0.004 s
% 0.21/0.47  % (30277)------------------------------
% 0.21/0.47  % (30277)------------------------------
% 0.21/0.48  % (30269)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f304,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f39,f45,f70,f282,f303])).
% 0.21/0.48  fof(f303,plain,(
% 0.21/0.48    ~spl4_1 | spl4_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f302])).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    $false | (~spl4_1 | spl4_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f301,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~v1_finset_1(k3_tarski(sK0)) | spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl4_2 <=> v1_finset_1(k3_tarski(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    v1_finset_1(k3_tarski(sK0)) | (~spl4_1 | spl4_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f298,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    v1_finset_1(sK0) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl4_1 <=> v1_finset_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f298,plain,(
% 0.21/0.48    ~v1_finset_1(sK0) | v1_finset_1(k3_tarski(sK0)) | (~spl4_1 | spl4_2)),
% 0.21/0.48    inference(resolution,[],[f297,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_finset_1(sK2(X0)) | ~v1_finset_1(X0) | v1_finset_1(k3_tarski(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) => v1_finset_1(k3_tarski(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_finset_1)).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    v1_finset_1(sK2(sK0)) | (~spl4_1 | spl4_2)),
% 0.21/0.48    inference(resolution,[],[f295,f291])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0),sK0) | (~spl4_1 | spl4_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f128,f37])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0),sK0) | v1_finset_1(k3_tarski(sK0)) | ~spl4_1),
% 0.21/0.48    inference(resolution,[],[f24,f34])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_finset_1(X0) | r2_hidden(sK2(X0),X0) | v1_finset_1(k3_tarski(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f295,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_hidden(X1,sK0) | v1_finset_1(X1)) ) | spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f18,f37])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X1] : (v1_finset_1(k3_tarski(sK0)) | ~r2_hidden(X1,sK0) | v1_finset_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : ((! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)) <~> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_finset_1)).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    ~spl4_1 | ~spl4_2 | spl4_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f281])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    $false | (~spl4_1 | ~spl4_2 | spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f280,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ~v1_finset_1(sK1) | spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl4_3 <=> v1_finset_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    v1_finset_1(sK1) | (~spl4_1 | ~spl4_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f279,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    v1_finset_1(k3_tarski(sK0)) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f36])).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    ~v1_finset_1(k3_tarski(sK0)) | v1_finset_1(sK1) | (~spl4_1 | ~spl4_2)),
% 0.21/0.48    inference(resolution,[],[f271,f26])).
% 0.21/0.48  % (30266)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_finset_1(X1) | v1_finset_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).
% 0.21/0.48  fof(f271,plain,(
% 0.21/0.48    r1_tarski(sK1,k3_tarski(sK0)) | (~spl4_1 | ~spl4_2)),
% 0.21/0.48    inference(resolution,[],[f178,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    r2_hidden(sK1,sK0) | (~spl4_1 | ~spl4_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f71,f34])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~v1_finset_1(sK0) | r2_hidden(sK1,sK0) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f19,f38])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK0) | r2_hidden(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r2_hidden(X2,X3) | r1_tarski(X2,k3_tarski(X3))) )),
% 0.21/0.48    inference(resolution,[],[f30,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f29,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl4_1 | ~spl4_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    $false | (spl4_1 | ~spl4_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ~v1_finset_1(sK0) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f32])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    v1_finset_1(sK0) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f48,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    v1_finset_1(k1_zfmisc_1(k3_tarski(sK0))) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f23,f38])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_finset_1(X0) | v1_finset_1(k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_finset_1(X0) => v1_finset_1(k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_finset_1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_finset_1(k1_zfmisc_1(k3_tarski(X0))) | v1_finset_1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f26,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~spl4_3 | ~spl4_1 | ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f36,f32,f42])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ~v1_finset_1(sK0) | ~v1_finset_1(sK1) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f20,f38])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ~v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK0) | ~v1_finset_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl4_1 | spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f36,f32])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v1_finset_1(k3_tarski(sK0)) | v1_finset_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (30269)------------------------------
% 0.21/0.48  % (30269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30269)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (30269)Memory used [KB]: 5500
% 0.21/0.48  % (30269)Time elapsed: 0.008 s
% 0.21/0.48  % (30269)------------------------------
% 0.21/0.48  % (30269)------------------------------
% 0.21/0.48  % (30259)Success in time 0.127 s
%------------------------------------------------------------------------------
