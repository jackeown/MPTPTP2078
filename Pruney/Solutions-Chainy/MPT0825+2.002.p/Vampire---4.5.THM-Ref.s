%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   28 (  32 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f22])).

fof(f22,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f21])).

fof(f21,plain,
    ( $false
    | spl1_1 ),
    inference(resolution,[],[f20,f16])).

fof(f16,plain,
    ( ~ r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f14,plain,
    ( spl1_1
  <=> r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f20,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(forward_demodulation,[],[f19,f10])).

fof(f10,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f19,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X0)) ),
    inference(forward_demodulation,[],[f18,f11])).

fof(f11,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f12,f9])).

fof(f9,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f17,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f8,f14])).

fof(f8,plain,(
    ~ r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f5])).

% (31016)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
fof(f5,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:55:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (31013)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (31014)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (31009)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (31009)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f17,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    spl1_1),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    $false | spl1_1),
% 0.22/0.44    inference(resolution,[],[f20,f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ~r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) | spl1_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    spl1_1 <=> r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f19,f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X0))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f18,f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))))) )),
% 0.22/0.44    inference(resolution,[],[f12,f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ~spl1_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f8,f14])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ~r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0] : ~r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  % (31016)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.22/0.44  fof(f4,conjecture,(
% 0.22/0.44    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relset_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (31009)------------------------------
% 0.22/0.44  % (31009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (31009)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (31009)Memory used [KB]: 10490
% 0.22/0.44  % (31009)Time elapsed: 0.004 s
% 0.22/0.44  % (31009)------------------------------
% 0.22/0.44  % (31009)------------------------------
% 0.22/0.44  % (31017)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.44  % (31006)Success in time 0.077 s
%------------------------------------------------------------------------------
