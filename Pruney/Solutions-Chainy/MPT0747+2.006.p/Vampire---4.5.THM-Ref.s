%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 133 expanded)
%              Number of leaves         :   10 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 285 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f152,f172])).

fof(f172,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl4_2 ),
    inference(resolution,[],[f41,f127])).

fof(f127,plain,(
    v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k3_tarski(sK0))))))) ),
    inference(resolution,[],[f121,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

% (14318)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
fof(f121,plain,(
    v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k3_tarski(sK0)))))) ),
    inference(resolution,[],[f105,f23])).

fof(f105,plain,(
    v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k3_tarski(sK0))))) ),
    inference(resolution,[],[f100,f23])).

fof(f100,plain,(
    v3_ordinal1(k1_ordinal1(k1_ordinal1(k3_tarski(sK0)))) ),
    inference(resolution,[],[f97,f23])).

fof(f97,plain,(
    v3_ordinal1(k1_ordinal1(k3_tarski(sK0))) ),
    inference(resolution,[],[f95,f23])).

fof(f95,plain,(
    v3_ordinal1(k3_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f93,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(X0))
      | v3_ordinal1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_ordinal1)).

fof(f93,plain,
    ( v3_ordinal1(k3_tarski(sK0))
    | v3_ordinal1(sK1(sK0)) ),
    inference(resolution,[],[f26,f21])).

fof(f21,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
    <=> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( r2_hidden(X1,X0)
          <=> v3_ordinal1(X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v3_ordinal1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,
    ( ! [X1] : ~ v3_ordinal1(X1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_2
  <=> ! [X1] : ~ v3_ordinal1(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f152,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f150,f116])).

fof(f116,plain,(
    r1_tarski(k1_ordinal1(k3_tarski(sK0)),k3_tarski(sK0)) ),
    inference(resolution,[],[f30,f101])).

fof(f101,plain,(
    r2_hidden(k1_ordinal1(k3_tarski(sK0)),sK0) ),
    inference(resolution,[],[f97,f20])).

fof(f20,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f150,plain,
    ( ~ r1_tarski(k1_ordinal1(k3_tarski(sK0)),k3_tarski(sK0))
    | spl4_1 ),
    inference(resolution,[],[f146,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f146,plain,
    ( r2_hidden(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0)))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f145,f95])).

fof(f145,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    | r2_hidden(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0)))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f140,f97])).

fof(f140,plain,
    ( ~ v3_ordinal1(k1_ordinal1(k3_tarski(sK0)))
    | ~ v3_ordinal1(k3_tarski(sK0))
    | r2_hidden(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0)))
    | spl4_1 ),
    inference(resolution,[],[f24,f99])).

fof(f99,plain,
    ( r1_ordinal1(k1_ordinal1(k3_tarski(sK0)),k1_ordinal1(k3_tarski(sK0)))
    | spl4_1 ),
    inference(resolution,[],[f97,f68])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_ordinal1(X0,X0) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f33,f38])).

fof(f38,plain,
    ( ~ sP3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_1
  <=> sP3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X0)
      | sP3 ) ),
    inference(cnf_transformation,[],[f33_D])).

fof(f33_D,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_ordinal1(X0,X0) )
  <=> ~ sP3 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f42,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f34,f40,f36])).

fof(f34,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | ~ sP3 ) ),
    inference(general_splitting,[],[f31,f33_D])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:47:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.47  % (14321)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.48  % (14310)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (14312)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.49  % (14312)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (14319)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f42,f152,f172])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    ~spl4_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f161])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    $false | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f41,f127])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k3_tarski(sK0)))))))),
% 0.22/0.49    inference(resolution,[],[f121,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.22/0.49  % (14318)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k3_tarski(sK0))))))),
% 0.22/0.49    inference(resolution,[],[f105,f23])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k3_tarski(sK0)))))),
% 0.22/0.49    inference(resolution,[],[f100,f23])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    v3_ordinal1(k1_ordinal1(k1_ordinal1(k3_tarski(sK0))))),
% 0.22/0.49    inference(resolution,[],[f97,f23])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    v3_ordinal1(k1_ordinal1(k3_tarski(sK0)))),
% 0.22/0.49    inference(resolution,[],[f95,f23])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    v3_ordinal1(k3_tarski(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f93,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_ordinal1(sK1(X0)) | v3_ordinal1(k3_tarski(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_ordinal1)).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    v3_ordinal1(k3_tarski(sK0)) | v3_ordinal1(sK1(sK0))),
% 0.22/0.49    inference(resolution,[],[f26,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | v3_ordinal1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : ! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ~! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : ~! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v3_ordinal1(k3_tarski(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X1] : (~v3_ordinal1(X1)) ) | ~spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    spl4_2 <=> ! [X1] : ~v3_ordinal1(X1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    spl4_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f151])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    $false | spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f150,f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    r1_tarski(k1_ordinal1(k3_tarski(sK0)),k3_tarski(sK0))),
% 0.22/0.49    inference(resolution,[],[f30,f101])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    r2_hidden(k1_ordinal1(k3_tarski(sK0)),sK0)),
% 0.22/0.49    inference(resolution,[],[f97,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X1] : (~v3_ordinal1(X1) | r2_hidden(X1,sK0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    ~r1_tarski(k1_ordinal1(k3_tarski(sK0)),k3_tarski(sK0)) | spl4_1),
% 0.22/0.49    inference(resolution,[],[f146,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    r2_hidden(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0))) | spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f145,f95])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ~v3_ordinal1(k3_tarski(sK0)) | r2_hidden(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0))) | spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f140,f97])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ~v3_ordinal1(k1_ordinal1(k3_tarski(sK0))) | ~v3_ordinal1(k3_tarski(sK0)) | r2_hidden(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0))) | spl4_1),
% 0.22/0.49    inference(resolution,[],[f24,f99])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    r1_ordinal1(k1_ordinal1(k3_tarski(sK0)),k1_ordinal1(k3_tarski(sK0))) | spl4_1),
% 0.22/0.49    inference(resolution,[],[f97,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(X0,X0)) ) | spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f33,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ~sP3 | spl4_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    spl4_1 <=> sP3),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(X0,X0) | sP3) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33_D])).
% 0.22/0.49  fof(f33_D,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(X0,X0)) ) <=> ~sP3),
% 0.22/0.49    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_ordinal1(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ~spl4_1 | spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f40,f36])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X1] : (~v3_ordinal1(X1) | ~sP3) )),
% 0.22/0.49    inference(general_splitting,[],[f31,f33_D])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_ordinal1(X0,X0) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => r1_ordinal1(X0,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (14312)------------------------------
% 0.22/0.49  % (14312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (14312)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (14312)Memory used [KB]: 5373
% 0.22/0.50  % (14312)Time elapsed: 0.013 s
% 0.22/0.50  % (14312)------------------------------
% 0.22/0.50  % (14312)------------------------------
% 0.22/0.50  % (14303)Success in time 0.131 s
%------------------------------------------------------------------------------
