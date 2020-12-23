%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  43 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 (  74 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f42])).

fof(f42,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f40])).

fof(f40,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_1 ),
    inference(superposition,[],[f33,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) ),
    inference(global_subsumption,[],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_xboole_0(k9_setfam_1(X0))
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) ) ),
    inference(resolution,[],[f17,f35])).

fof(f35,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(resolution,[],[f29,f14])).

fof(f14,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f29,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k9_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f18,f15])).

fof(f15,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f17,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f37,plain,(
    ! [X1] : ~ v1_xboole_0(k9_setfam_1(X1)) ),
    inference(resolution,[],[f35,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

% (16708)Termination reason: Refutation not found, incomplete strategy
fof(f33,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

% (16708)Memory used [KB]: 10618
fof(f31,plain,
    ( spl2_1
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

% (16708)Time elapsed: 0.103 s
% (16708)------------------------------
% (16708)------------------------------
fof(f34,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f31])).

fof(f23,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f16,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f13,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:26:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (16724)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.49  % (16716)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.49  % (16708)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (16716)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (16708)Refutation not found, incomplete strategy% (16708)------------------------------
% 0.20/0.50  % (16708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f34,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    spl2_1),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    $false | spl2_1),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    k1_xboole_0 != k1_xboole_0 | spl2_1),
% 0.20/0.50    inference(superposition,[],[f33,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.50    inference(global_subsumption,[],[f37,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (v1_xboole_0(k9_setfam_1(X0)) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.50    inference(resolution,[],[f17,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(k1_xboole_0,k9_setfam_1(X0))) )),
% 0.20/0.50    inference(resolution,[],[f29,f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k9_setfam_1(X0))) )),
% 0.20/0.50    inference(equality_resolution,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k9_setfam_1(X0) != X1) )),
% 0.20/0.50    inference(definition_unfolding,[],[f18,f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X1] : (~v1_xboole_0(k9_setfam_1(X1))) )),
% 0.20/0.50    inference(resolution,[],[f35,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.20/0.50  % (16708)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) | spl2_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f31])).
% 0.20/0.50  
% 0.20/0.50  % (16708)Memory used [KB]: 10618
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    spl2_1 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.50  % (16708)Time elapsed: 0.103 s
% 0.20/0.50  % (16708)------------------------------
% 0.20/0.50  % (16708)------------------------------
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ~spl2_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f23,f31])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.20/0.50    inference(definition_unfolding,[],[f13,f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (16716)------------------------------
% 0.20/0.50  % (16716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16716)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (16716)Memory used [KB]: 10618
% 0.20/0.50  % (16716)Time elapsed: 0.095 s
% 0.20/0.50  % (16716)------------------------------
% 0.20/0.50  % (16716)------------------------------
% 0.20/0.50  % (16698)Success in time 0.148 s
%------------------------------------------------------------------------------
