%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 (  98 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 157 expanded)
%              Number of equality atoms :   54 (  78 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f304,f307,f315])).

fof(f315,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f110,f299,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f176,f113])).

fof(f113,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k9_setfam_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f62,f42])).

fof(f42,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f176,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(superposition,[],[f118,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f85,f90])).

fof(f90,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f50,f37])).

fof(f37,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f85,plain,(
    ! [X0] : o_0_0_xboole_0 = k6_subset_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f41,f37,f54,f37])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f118,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k6_subset_1(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k6_subset_1(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f76,f54,f80])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f299,plain,
    ( v1_xboole_0(k9_setfam_1(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl3_7
  <=> v1_xboole_0(k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f307,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f110,f303,f113])).

fof(f303,plain,
    ( ~ r2_hidden(sK0,k9_setfam_1(sK0))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl3_8
  <=> r2_hidden(sK0,k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f304,plain,
    ( spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f295,f301,f297])).

fof(f295,plain,
    ( ~ r2_hidden(sK0,k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f294])).

fof(f294,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(superposition,[],[f81,f293])).

fof(f293,plain,(
    ! [X0] :
      ( k4_yellow_0(k3_lattice3(k1_lattice3(X0))) = X0
      | ~ r2_hidden(X0,k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f292,f86])).

fof(f86,plain,(
    ! [X0] : k3_tarski(k9_setfam_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f43,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f292,plain,(
    ! [X0] :
      ( k4_yellow_0(k3_lattice3(k1_lattice3(X0))) = X0
      | ~ r2_hidden(k3_tarski(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f291,f86])).

fof(f291,plain,(
    ! [X0] :
      ( k3_tarski(k9_setfam_1(X0)) = k4_yellow_0(k3_lattice3(k1_lattice3(X0)))
      | ~ r2_hidden(k3_tarski(k9_setfam_1(X0)),k9_setfam_1(X0))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(superposition,[],[f89,f88])).

fof(f88,plain,(
    ! [X0] : k3_lattice3(k1_lattice3(X0)) = g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) ),
    inference(definition_unfolding,[],[f46,f45,f48])).

fof(f48,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f45,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f46,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f89,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(g1_orders_2(X0,k1_yellow_1(X0)))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f81,plain,(
    sK0 != k4_yellow_0(k3_lattice3(k1_lattice3(sK0))) ),
    inference(definition_unfolding,[],[f36,f45])).

fof(f36,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (22139)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.49  % (22123)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.49  % (22147)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.49  % (22139)Refutation not found, incomplete strategy% (22139)------------------------------
% 0.20/0.49  % (22139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22147)Refutation not found, incomplete strategy% (22147)------------------------------
% 0.20/0.49  % (22147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22139)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (22139)Memory used [KB]: 1663
% 0.20/0.49  % (22139)Time elapsed: 0.113 s
% 0.20/0.49  % (22139)------------------------------
% 0.20/0.49  % (22139)------------------------------
% 0.20/0.50  % (22133)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (22147)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (22147)Memory used [KB]: 6140
% 0.20/0.50  % (22147)Time elapsed: 0.108 s
% 0.20/0.50  % (22147)------------------------------
% 0.20/0.50  % (22147)------------------------------
% 0.20/0.50  % (22125)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (22121)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (22133)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f304,f307,f315])).
% 0.20/0.50  fof(f315,plain,(
% 0.20/0.50    ~spl3_7),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f309])).
% 0.20/0.50  fof(f309,plain,(
% 0.20/0.50    $false | ~spl3_7),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f110,f299,f178])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v1_xboole_0(k9_setfam_1(X0))) )),
% 0.20/0.50    inference(resolution,[],[f176,f113])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    ( ! [X2,X0] : (r2_hidden(X2,k9_setfam_1(X0)) | ~r1_tarski(X2,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k9_setfam_1(X0) != X1) )),
% 0.20/0.50    inference(definition_unfolding,[],[f62,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,axiom,(
% 0.20/0.50    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~r2_hidden(X2,X1) | ~v1_xboole_0(X1)) )),
% 0.20/0.50    inference(superposition,[],[f118,f122])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k6_subset_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(superposition,[],[f85,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ( ! [X0] : (o_0_0_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f50,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    k1_xboole_0 = o_0_0_xboole_0),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    k1_xboole_0 = o_0_0_xboole_0),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X0] : (o_0_0_xboole_0 = k6_subset_1(o_0_0_xboole_0,X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f41,f37,f54,f37])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~r2_hidden(X2,k6_subset_1(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f108])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k6_subset_1(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f76,f54,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f47,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f56,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    v1_xboole_0(k9_setfam_1(sK0)) | ~spl3_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f297])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    spl3_7 <=> v1_xboole_0(k9_setfam_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f307,plain,(
% 0.20/0.50    spl3_8),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f305])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    $false | spl3_8),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f110,f303,f113])).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    ~r2_hidden(sK0,k9_setfam_1(sK0)) | spl3_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f301])).
% 0.20/0.50  fof(f301,plain,(
% 0.20/0.50    spl3_8 <=> r2_hidden(sK0,k9_setfam_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    spl3_7 | ~spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f295,f301,f297])).
% 0.20/0.50  fof(f295,plain,(
% 0.20/0.50    ~r2_hidden(sK0,k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f294])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    sK0 != sK0 | ~r2_hidden(sK0,k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 0.20/0.50    inference(superposition,[],[f81,f293])).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    ( ! [X0] : (k4_yellow_0(k3_lattice3(k1_lattice3(X0))) = X0 | ~r2_hidden(X0,k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f292,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = X0) )),
% 0.20/0.50    inference(definition_unfolding,[],[f43,f42])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    ( ! [X0] : (k4_yellow_0(k3_lattice3(k1_lattice3(X0))) = X0 | ~r2_hidden(k3_tarski(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f291,f86])).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = k4_yellow_0(k3_lattice3(k1_lattice3(X0))) | ~r2_hidden(k3_tarski(k9_setfam_1(X0)),k9_setfam_1(X0)) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.20/0.50    inference(superposition,[],[f89,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X0] : (k3_lattice3(k1_lattice3(X0)) = g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f46,f45,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,axiom,(
% 0.20/0.50    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,axiom,(
% 0.20/0.50    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,axiom,(
% 0.20/0.50    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(g1_orders_2(X0,k1_yellow_1(X0))) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f49,f48])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (v1_xboole_0(X0) | ~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,axiom,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    sK0 != k4_yellow_0(k3_lattice3(k1_lattice3(sK0)))),
% 0.20/0.50    inference(definition_unfolding,[],[f36,f45])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0),
% 0.20/0.50    inference(ennf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,negated_conjecture,(
% 0.20/0.50    ~! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.20/0.50    inference(negated_conjecture,[],[f26])).
% 0.20/0.50  fof(f26,conjecture,(
% 0.20/0.50    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (22133)------------------------------
% 0.20/0.50  % (22133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (22133)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (22133)Memory used [KB]: 6396
% 0.20/0.50  % (22133)Time elapsed: 0.116 s
% 0.20/0.50  % (22133)------------------------------
% 0.20/0.50  % (22133)------------------------------
% 0.20/0.50  % (22114)Success in time 0.151 s
%------------------------------------------------------------------------------
