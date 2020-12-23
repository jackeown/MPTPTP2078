%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:07 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 112 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  128 ( 259 expanded)
%              Number of equality atoms :   37 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f78,f80])).

fof(f80,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f79])).

% (10313)Refutation not found, incomplete strategy% (10313)------------------------------
% (10313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10313)Termination reason: Refutation not found, incomplete strategy

% (10313)Memory used [KB]: 1663
% (10313)Time elapsed: 0.127 s
% (10313)------------------------------
% (10313)------------------------------
fof(f79,plain,
    ( $false
    | ~ spl2_1 ),
    inference(resolution,[],[f52,f21])).

fof(f21,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK0,sK1)
    & ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    & v1_zfmisc_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK0,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
      & v1_zfmisc_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ~ r1_tarski(sK0,X1)
        & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
   => ( ~ r1_tarski(sK0,sK1)
      & ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

fof(f52,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f78,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | ~ spl2_2 ),
    inference(resolution,[],[f75,f24])).

fof(f24,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f33,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f71,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f42,f40])).

fof(f40,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f71,plain,
    ( k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f43,f62])).

fof(f62,plain,
    ( sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f57,f39])).

fof(f39,plain,(
    ~ v1_xboole_0(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f23,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f23,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)))
        | sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)) )
    | ~ spl2_2 ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f55,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_xboole_0(X0)
        | sK0 = X0 )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_2
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_xboole_0(X0)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f56,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f48,f54,f50])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:11:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (10325)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (10341)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (10313)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.54  % (10314)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.54  % (10325)Refutation found. Thanks to Tanya!
% 1.35/0.54  % SZS status Theorem for theBenchmark
% 1.35/0.54  % SZS output start Proof for theBenchmark
% 1.35/0.54  fof(f81,plain,(
% 1.35/0.54    $false),
% 1.35/0.54    inference(avatar_sat_refutation,[],[f56,f78,f80])).
% 1.35/0.54  fof(f80,plain,(
% 1.35/0.54    ~spl2_1),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f79])).
% 1.35/0.54  % (10313)Refutation not found, incomplete strategy% (10313)------------------------------
% 1.35/0.54  % (10313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (10313)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (10313)Memory used [KB]: 1663
% 1.35/0.54  % (10313)Time elapsed: 0.127 s
% 1.35/0.54  % (10313)------------------------------
% 1.35/0.54  % (10313)------------------------------
% 1.35/0.54  fof(f79,plain,(
% 1.35/0.54    $false | ~spl2_1),
% 1.35/0.54    inference(resolution,[],[f52,f21])).
% 1.35/0.54  fof(f21,plain,(
% 1.35/0.54    ~v1_xboole_0(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f19])).
% 1.35/0.54  fof(f19,plain,(
% 1.35/0.54    (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0)),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18,f17])).
% 1.35/0.54  fof(f17,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f18,plain,(
% 1.35/0.54    ? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) => (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1)))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f14,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 1.35/0.54    inference(flattening,[],[f13])).
% 1.35/0.54  fof(f13,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f12])).
% 1.35/0.54  fof(f12,negated_conjecture,(
% 1.35/0.54    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.35/0.54    inference(negated_conjecture,[],[f11])).
% 1.35/0.54  fof(f11,conjecture,(
% 1.35/0.54    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).
% 1.35/0.54  fof(f52,plain,(
% 1.35/0.54    v1_xboole_0(sK0) | ~spl2_1),
% 1.35/0.54    inference(avatar_component_clause,[],[f50])).
% 1.35/0.54  fof(f50,plain,(
% 1.35/0.54    spl2_1 <=> v1_xboole_0(sK0)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.35/0.54  fof(f78,plain,(
% 1.35/0.54    ~spl2_2),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f76])).
% 1.35/0.54  fof(f76,plain,(
% 1.35/0.54    $false | ~spl2_2),
% 1.35/0.54    inference(resolution,[],[f75,f24])).
% 1.35/0.54  fof(f24,plain,(
% 1.35/0.54    ~r1_tarski(sK0,sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f19])).
% 1.35/0.54  fof(f75,plain,(
% 1.35/0.54    r1_tarski(sK0,sK1) | ~spl2_2),
% 1.35/0.54    inference(trivial_inequality_removal,[],[f74])).
% 1.35/0.54  fof(f74,plain,(
% 1.35/0.54    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) | ~spl2_2),
% 1.35/0.54    inference(superposition,[],[f33,f73])).
% 1.35/0.54  fof(f73,plain,(
% 1.35/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl2_2),
% 1.35/0.54    inference(forward_demodulation,[],[f71,f45])).
% 1.35/0.54  fof(f45,plain,(
% 1.35/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.35/0.54    inference(superposition,[],[f42,f40])).
% 1.35/0.54  fof(f40,plain,(
% 1.35/0.54    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.35/0.54    inference(definition_unfolding,[],[f25,f38])).
% 1.35/0.54  fof(f38,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f29,f36])).
% 1.35/0.54  fof(f36,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f31,f35])).
% 1.35/0.54  fof(f35,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f7])).
% 1.35/0.54  fof(f7,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.35/0.54  fof(f31,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f6])).
% 1.35/0.54  fof(f6,axiom,(
% 1.35/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.35/0.54  fof(f29,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f8])).
% 1.35/0.54  fof(f8,axiom,(
% 1.35/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.35/0.54  fof(f25,plain,(
% 1.35/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.35/0.54    inference(cnf_transformation,[],[f3])).
% 1.35/0.54  fof(f3,axiom,(
% 1.35/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.35/0.54  fof(f42,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f28,f38])).
% 1.35/0.54  fof(f28,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f4])).
% 1.35/0.54  fof(f4,axiom,(
% 1.35/0.54    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.35/0.54  fof(f71,plain,(
% 1.35/0.54    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1) | ~spl2_2),
% 1.35/0.54    inference(superposition,[],[f43,f62])).
% 1.35/0.54  fof(f62,plain,(
% 1.35/0.54    sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl2_2),
% 1.35/0.54    inference(resolution,[],[f57,f39])).
% 1.35/0.54  fof(f39,plain,(
% 1.35/0.54    ~v1_xboole_0(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.35/0.54    inference(definition_unfolding,[],[f23,f37])).
% 1.35/0.54  fof(f37,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f30,f36])).
% 1.35/0.54  fof(f30,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f9])).
% 1.35/0.54  fof(f9,axiom,(
% 1.35/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.35/0.54  fof(f23,plain,(
% 1.35/0.54    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 1.35/0.54    inference(cnf_transformation,[],[f19])).
% 1.35/0.54  fof(f57,plain,(
% 1.35/0.54    ( ! [X0] : (v1_xboole_0(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))) | sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))) ) | ~spl2_2),
% 1.35/0.54    inference(resolution,[],[f55,f41])).
% 1.35/0.54  fof(f41,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f27,f37])).
% 1.35/0.54  fof(f27,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f2])).
% 1.35/0.54  fof(f2,axiom,(
% 1.35/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.35/0.54  fof(f55,plain,(
% 1.35/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0) ) | ~spl2_2),
% 1.35/0.54    inference(avatar_component_clause,[],[f54])).
% 1.35/0.54  fof(f54,plain,(
% 1.35/0.54    spl2_2 <=> ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.35/0.54  fof(f43,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f32,f37])).
% 1.35/0.54  fof(f32,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f5])).
% 1.35/0.54  fof(f5,axiom,(
% 1.35/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.35/0.54  fof(f33,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f20])).
% 1.35/0.54  fof(f20,plain,(
% 1.35/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.35/0.54    inference(nnf_transformation,[],[f1])).
% 1.35/0.54  fof(f1,axiom,(
% 1.35/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.35/0.54  fof(f56,plain,(
% 1.35/0.54    spl2_1 | spl2_2),
% 1.35/0.54    inference(avatar_split_clause,[],[f48,f54,f50])).
% 1.35/0.54  fof(f48,plain,(
% 1.35/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 1.35/0.54    inference(resolution,[],[f26,f22])).
% 1.35/0.54  fof(f22,plain,(
% 1.35/0.54    v1_zfmisc_1(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f19])).
% 1.35/0.54  fof(f26,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f16])).
% 1.35/0.54  fof(f16,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.35/0.54    inference(flattening,[],[f15])).
% 1.35/0.54  fof(f15,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.35/0.54    inference(ennf_transformation,[],[f10])).
% 1.35/0.54  fof(f10,axiom,(
% 1.35/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.35/0.54  % SZS output end Proof for theBenchmark
% 1.35/0.54  % (10325)------------------------------
% 1.35/0.54  % (10325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (10325)Termination reason: Refutation
% 1.35/0.54  
% 1.35/0.54  % (10325)Memory used [KB]: 6268
% 1.35/0.54  % (10325)Time elapsed: 0.091 s
% 1.35/0.54  % (10325)------------------------------
% 1.35/0.54  % (10325)------------------------------
% 1.35/0.54  % (10312)Success in time 0.177 s
%------------------------------------------------------------------------------
