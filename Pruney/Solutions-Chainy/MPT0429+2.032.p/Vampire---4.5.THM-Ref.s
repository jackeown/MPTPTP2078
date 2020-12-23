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
% DateTime   : Thu Dec  3 12:46:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   79 (  92 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f52,f56,f63])).

fof(f63,plain,
    ( spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f57,f59])).

fof(f59,plain,
    ( ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(unit_resulting_resolution,[],[f35,f39,f55])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f39,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl1_3
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f35,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl1_2
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f57,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl1_1
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f31,f51])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f31,plain,
    ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl1_1
  <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f56,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f52,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f40,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f36,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f32,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f19,f29])).

fof(f19,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).

fof(f17,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:17:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.49  % (29064)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (29064)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f32,f36,f40,f52,f56,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_6 | ~spl1_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    $false | (spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_6 | ~spl1_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f57,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) ) | (~spl1_2 | ~spl1_3 | ~spl1_7)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f35,f39,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) ) | ~spl1_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl1_7 <=> ! [X1,X0] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl1_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl1_3 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl1_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    spl1_2 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | (spl1_1 | ~spl1_6)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f31,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) ) | ~spl1_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl1_6 <=> ! [X1,X0] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl1_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    spl1_1 <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl1_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f54])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl1_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f50])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    spl1_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f21,f38])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    spl1_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f20,f34])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ~spl1_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f19,f29])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) => ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (29064)------------------------------
% 0.22/0.49  % (29064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (29064)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (29064)Memory used [KB]: 6140
% 0.22/0.49  % (29064)Time elapsed: 0.051 s
% 0.22/0.49  % (29064)------------------------------
% 0.22/0.49  % (29064)------------------------------
% 0.22/0.49  % (29075)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (29071)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (29058)Success in time 0.121 s
%------------------------------------------------------------------------------
