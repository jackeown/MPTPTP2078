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
% DateTime   : Thu Dec  3 13:20:07 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 164 expanded)
%              Number of leaves         :   15 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  141 ( 330 expanded)
%              Number of equality atoms :   35 ( 108 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f128,f132,f198,f200])).

fof(f200,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl2_1 ),
    inference(resolution,[],[f113,f21])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

fof(f113,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f198,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl2_3 ),
    inference(resolution,[],[f194,f24])).

fof(f24,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f194,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_3 ),
    inference(trivial_inequality_removal,[],[f185])).

fof(f185,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1)
    | ~ spl2_3 ),
    inference(superposition,[],[f32,f149])).

fof(f149,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f135,f136])).

fof(f136,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl2_3 ),
    inference(superposition,[],[f45,f123])).

fof(f123,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_3
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f45,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(resolution,[],[f33,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f135,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0)
    | ~ spl2_3 ),
    inference(superposition,[],[f43,f123])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f40,f41])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f132,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f127,f44])).

fof(f127,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl2_4
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f128,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f119,f115,f125,f121])).

fof(f115,plain,
    ( spl2_2
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_xboole_0(X0)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f119,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f116,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f37,f41])).

fof(f37,plain,(
    ~ v1_xboole_0(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f23,f36])).

fof(f23,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f116,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ r1_tarski(X0,sK0)
        | sK0 = X0 )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f109,f115,f111])).

fof(f109,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f25,f22])).

fof(f22,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 17:00:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.53  % (28481)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.54  % (28490)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.54  % (28481)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % (28490)Refutation not found, incomplete strategy% (28490)------------------------------
% 0.23/0.54  % (28490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (28490)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (28490)Memory used [KB]: 1663
% 0.23/0.54  % (28490)Time elapsed: 0.100 s
% 0.23/0.54  % (28490)------------------------------
% 0.23/0.54  % (28490)------------------------------
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f201,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(avatar_sat_refutation,[],[f117,f128,f132,f198,f200])).
% 0.23/0.55  fof(f200,plain,(
% 0.23/0.55    ~spl2_1),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f199])).
% 0.23/0.55  fof(f199,plain,(
% 0.23/0.55    $false | ~spl2_1),
% 0.23/0.55    inference(resolution,[],[f113,f21])).
% 0.23/0.55  fof(f21,plain,(
% 0.23/0.55    ~v1_xboole_0(sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f19])).
% 0.23/0.55  fof(f19,plain,(
% 0.23/0.55    (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0)),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18,f17])).
% 0.23/0.55  fof(f17,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f18,plain,(
% 0.23/0.55    ? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) => (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1)))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f14,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 0.23/0.55    inference(flattening,[],[f13])).
% 0.23/0.55  fof(f13,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f11])).
% 0.23/0.55  fof(f11,negated_conjecture,(
% 0.23/0.55    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.23/0.55    inference(negated_conjecture,[],[f10])).
% 0.23/0.55  fof(f10,conjecture,(
% 0.23/0.55    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).
% 0.23/0.55  fof(f113,plain,(
% 0.23/0.55    v1_xboole_0(sK0) | ~spl2_1),
% 0.23/0.55    inference(avatar_component_clause,[],[f111])).
% 0.23/0.55  fof(f111,plain,(
% 0.23/0.55    spl2_1 <=> v1_xboole_0(sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.55  fof(f198,plain,(
% 0.23/0.55    ~spl2_3),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f196])).
% 0.23/0.55  fof(f196,plain,(
% 0.23/0.55    $false | ~spl2_3),
% 0.23/0.55    inference(resolution,[],[f194,f24])).
% 0.23/0.55  fof(f24,plain,(
% 0.23/0.55    ~r1_tarski(sK0,sK1)),
% 0.23/0.55    inference(cnf_transformation,[],[f19])).
% 0.23/0.55  fof(f194,plain,(
% 0.23/0.55    r1_tarski(sK0,sK1) | ~spl2_3),
% 0.23/0.55    inference(trivial_inequality_removal,[],[f185])).
% 0.23/0.55  fof(f185,plain,(
% 0.23/0.55    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) | ~spl2_3),
% 0.23/0.55    inference(superposition,[],[f32,f149])).
% 0.23/0.55  fof(f149,plain,(
% 0.23/0.55    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl2_3),
% 0.23/0.55    inference(backward_demodulation,[],[f135,f136])).
% 0.23/0.55  fof(f136,plain,(
% 0.23/0.55    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl2_3),
% 0.23/0.55    inference(superposition,[],[f45,f123])).
% 0.23/0.55  fof(f123,plain,(
% 0.23/0.55    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_3),
% 0.23/0.55    inference(avatar_component_clause,[],[f121])).
% 0.23/0.55  fof(f121,plain,(
% 0.23/0.55    spl2_3 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.55  fof(f45,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.23/0.55    inference(resolution,[],[f33,f44])).
% 0.23/0.55  fof(f44,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.23/0.55    inference(backward_demodulation,[],[f39,f41])).
% 0.23/0.55  fof(f41,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.23/0.55    inference(definition_unfolding,[],[f31,f36])).
% 0.23/0.55  fof(f36,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.23/0.55    inference(definition_unfolding,[],[f28,f35])).
% 0.23/0.55  fof(f35,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.23/0.55    inference(definition_unfolding,[],[f29,f34])).
% 0.23/0.55  fof(f34,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f7])).
% 0.23/0.55  fof(f7,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.55  fof(f29,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f6])).
% 0.23/0.55  fof(f6,axiom,(
% 0.23/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.55  fof(f28,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f8])).
% 0.23/0.55  fof(f8,axiom,(
% 0.23/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.55  fof(f31,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f5])).
% 0.23/0.55  fof(f5,axiom,(
% 0.23/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.55  fof(f39,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.23/0.55    inference(definition_unfolding,[],[f27,f36])).
% 0.23/0.55  fof(f27,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f3])).
% 0.23/0.55  fof(f3,axiom,(
% 0.23/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.23/0.55  fof(f33,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f20])).
% 0.23/0.55  fof(f20,plain,(
% 0.23/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.23/0.55    inference(nnf_transformation,[],[f2])).
% 0.23/0.55  fof(f2,axiom,(
% 0.23/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.23/0.55  fof(f135,plain,(
% 0.23/0.55    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0) | ~spl2_3),
% 0.23/0.55    inference(superposition,[],[f43,f123])).
% 0.23/0.55  fof(f43,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.23/0.55    inference(backward_demodulation,[],[f40,f41])).
% 0.23/0.55  fof(f40,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.23/0.55    inference(definition_unfolding,[],[f30,f36])).
% 0.23/0.55  fof(f30,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f4])).
% 0.23/0.55  fof(f4,axiom,(
% 0.23/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.23/0.55  fof(f32,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f20])).
% 0.23/0.55  fof(f132,plain,(
% 0.23/0.55    spl2_4),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f129])).
% 0.23/0.55  fof(f129,plain,(
% 0.23/0.55    $false | spl2_4),
% 0.23/0.55    inference(resolution,[],[f127,f44])).
% 0.23/0.55  fof(f127,plain,(
% 0.23/0.55    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | spl2_4),
% 0.23/0.55    inference(avatar_component_clause,[],[f125])).
% 0.23/0.55  fof(f125,plain,(
% 0.23/0.55    spl2_4 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.55  fof(f128,plain,(
% 0.23/0.55    spl2_3 | ~spl2_4 | ~spl2_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f119,f115,f125,f121])).
% 0.23/0.55  fof(f115,plain,(
% 0.23/0.55    spl2_2 <=> ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.55  fof(f119,plain,(
% 0.23/0.55    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_2),
% 0.23/0.55    inference(resolution,[],[f116,f42])).
% 0.23/0.55  fof(f42,plain,(
% 0.23/0.55    ~v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.23/0.55    inference(backward_demodulation,[],[f37,f41])).
% 0.23/0.55  fof(f37,plain,(
% 0.23/0.55    ~v1_xboole_0(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.23/0.55    inference(definition_unfolding,[],[f23,f36])).
% 0.23/0.55  fof(f23,plain,(
% 0.23/0.55    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 0.23/0.55    inference(cnf_transformation,[],[f19])).
% 0.23/0.55  fof(f116,plain,(
% 0.23/0.55    ( ! [X0] : (v1_xboole_0(X0) | ~r1_tarski(X0,sK0) | sK0 = X0) ) | ~spl2_2),
% 0.23/0.55    inference(avatar_component_clause,[],[f115])).
% 0.23/0.55  fof(f117,plain,(
% 0.23/0.55    spl2_1 | spl2_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f109,f115,f111])).
% 0.23/0.55  fof(f109,plain,(
% 0.23/0.55    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 0.23/0.55    inference(resolution,[],[f25,f22])).
% 0.23/0.55  fof(f22,plain,(
% 0.23/0.55    v1_zfmisc_1(sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f19])).
% 0.23/0.55  fof(f25,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f16])).
% 0.23/0.55  fof(f16,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.23/0.55    inference(flattening,[],[f15])).
% 0.23/0.55  fof(f15,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f9])).
% 0.23/0.55  fof(f9,axiom,(
% 0.23/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.23/0.55  % SZS output end Proof for theBenchmark
% 0.23/0.55  % (28481)------------------------------
% 0.23/0.55  % (28481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (28481)Termination reason: Refutation
% 0.23/0.55  
% 0.23/0.55  % (28481)Memory used [KB]: 6268
% 0.23/0.55  % (28481)Time elapsed: 0.106 s
% 0.23/0.55  % (28481)------------------------------
% 0.23/0.55  % (28481)------------------------------
% 0.23/0.55  % (28468)Success in time 0.176 s
%------------------------------------------------------------------------------
