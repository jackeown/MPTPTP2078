%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 (  98 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f28,f32,f36,f40,f47,f49])).

fof(f49,plain,
    ( spl1_1
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | spl1_1
    | ~ spl1_7 ),
    inference(resolution,[],[f46,f19])).

fof(f19,plain,
    ( ~ r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl1_1
  <=> r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f46,plain,
    ( ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl1_7
  <=> ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f47,plain,
    ( spl1_7
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f43,f38,f34,f30,f26,f45])).

fof(f26,plain,
    ( spl1_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f30,plain,
    ( spl1_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f34,plain,
    ( spl1_5
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f38,plain,
    ( spl1_6
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f43,plain,
    ( ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f42,f35])).

fof(f35,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f34])).

fof(f42,plain,
    ( ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X0))
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f41,f31])).

fof(f31,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f30])).

fof(f41,plain,
    ( ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))))
    | ~ spl1_3
    | ~ spl1_6 ),
    inference(resolution,[],[f39,f27])).

fof(f27,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f26])).

fof(f39,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f38])).

fof(f40,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f15,f38])).

fof(f15,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f36,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f13,f34])).

fof(f13,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f32,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f28,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f11,f26])).

fof(f11,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f20,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f10,f17])).

fof(f10,plain,(
    ~ r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ~ r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).

fof(f8,plain,
    ( ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:47:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (27423)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.44  % (27424)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.44  % (27420)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (27420)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f20,f28,f32,f36,f40,f47,f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    spl1_1 | ~spl1_7),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f48])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    $false | (spl1_1 | ~spl1_7)),
% 0.22/0.44    inference(resolution,[],[f46,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ~r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) | spl1_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    spl1_1 <=> r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))) ) | ~spl1_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    spl1_7 <=> ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    spl1_7 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f43,f38,f34,f30,f26,f45])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    spl1_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    spl1_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    spl1_5 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    spl1_6 <=> ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))) ) | (~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_6)),
% 0.22/0.44    inference(forward_demodulation,[],[f42,f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f34])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X0))) ) | (~spl1_3 | ~spl1_4 | ~spl1_6)),
% 0.22/0.44    inference(forward_demodulation,[],[f41,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f30])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))))) ) | (~spl1_3 | ~spl1_6)),
% 0.22/0.44    inference(resolution,[],[f39,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f26])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) | ~spl1_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f38])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl1_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f15,f38])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    spl1_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f13,f34])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    spl1_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f14,f30])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    spl1_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f11,f26])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ~spl1_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f10,f17])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ~r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ~r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0] : ~r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0] : ~r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.22/0.44  fof(f4,conjecture,(
% 0.22/0.44    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relset_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (27420)------------------------------
% 0.22/0.44  % (27420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (27420)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (27420)Memory used [KB]: 10490
% 0.22/0.44  % (27420)Time elapsed: 0.004 s
% 0.22/0.44  % (27420)------------------------------
% 0.22/0.44  % (27420)------------------------------
% 0.22/0.44  % (27414)Success in time 0.075 s
%------------------------------------------------------------------------------
