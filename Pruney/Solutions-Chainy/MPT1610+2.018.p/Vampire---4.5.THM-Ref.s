%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 (  86 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f47,f49,f52])).

fof(f52,plain,(
    ~ spl1_1 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | ~ spl1_1 ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f22,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f20,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f36,plain,
    ( v1_xboole_0(k9_setfam_1(sK0))
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl1_1
  <=> v1_xboole_0(k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f49,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | spl1_3 ),
    inference(resolution,[],[f46,f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f46,plain,
    ( ~ m1_subset_1(k1_xboole_0,k9_setfam_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl1_3
  <=> m1_subset_1(k1_xboole_0,k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f47,plain,
    ( ~ spl1_3
    | spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f42,f38,f34,f44])).

fof(f38,plain,
    ( spl1_2
  <=> r2_hidden(k1_xboole_0,k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f42,plain,
    ( v1_xboole_0(k9_setfam_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k9_setfam_1(sK0))
    | spl1_2 ),
    inference(resolution,[],[f40,f25])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f40,plain,
    ( ~ r2_hidden(k1_xboole_0,k9_setfam_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f41,plain,
    ( spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f32,f38,f34])).

fof(f32,plain,
    ( ~ r2_hidden(k1_xboole_0,k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(superposition,[],[f27,f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f27,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f23,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f19,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f17])).

fof(f17,plain,
    ( ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))
   => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:43:02 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (7687)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.45  % (7687)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f41,f47,f49,f52])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    ~spl1_1),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f51])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    $false | ~spl1_1),
% 0.22/0.45    inference(resolution,[],[f36,f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f20,f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    v1_xboole_0(k9_setfam_1(sK0)) | ~spl1_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    spl1_1 <=> v1_xboole_0(k9_setfam_1(sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    spl1_3),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f48])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    $false | spl1_3),
% 0.22/0.45    inference(resolution,[],[f46,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(k1_xboole_0,k9_setfam_1(X0))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f21,f22])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    ~m1_subset_1(k1_xboole_0,k9_setfam_1(sK0)) | spl1_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f44])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    spl1_3 <=> m1_subset_1(k1_xboole_0,k9_setfam_1(sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    ~spl1_3 | spl1_1 | spl1_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f42,f38,f34,f44])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    spl1_2 <=> r2_hidden(k1_xboole_0,k9_setfam_1(sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    v1_xboole_0(k9_setfam_1(sK0)) | ~m1_subset_1(k1_xboole_0,k9_setfam_1(sK0)) | spl1_2),
% 0.22/0.45    inference(resolution,[],[f40,f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ~r2_hidden(k1_xboole_0,k9_setfam_1(sK0)) | spl1_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f38])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    spl1_1 | ~spl1_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f32,f38,f34])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ~r2_hidden(k1_xboole_0,k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 0.22/0.45    inference(trivial_inequality_removal,[],[f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(k1_xboole_0,k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 0.22/0.45    inference(superposition,[],[f27,f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.22/0.45    inference(definition_unfolding,[],[f19,f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,negated_conjecture,(
% 0.22/0.45    ~! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.45    inference(negated_conjecture,[],[f8])).
% 0.22/0.45  fof(f8,conjecture,(
% 0.22/0.45    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (7687)------------------------------
% 0.22/0.45  % (7687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (7687)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (7687)Memory used [KB]: 6012
% 0.22/0.45  % (7687)Time elapsed: 0.004 s
% 0.22/0.45  % (7687)------------------------------
% 0.22/0.45  % (7687)------------------------------
% 0.22/0.45  % (7682)Success in time 0.087 s
%------------------------------------------------------------------------------
