%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 319 expanded)
%              Number of leaves         :   14 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  111 ( 419 expanded)
%              Number of equality atoms :   72 ( 346 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f207,f213])).

fof(f213,plain,
    ( spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f96,f78,f98])).

fof(f98,plain,
    ( spl2_3
  <=> ! [X8,X10] :
        ( k1_setfam_1(k2_xboole_0(X10,k2_enumset1(X8,X8,X8,X8))) = k4_xboole_0(k1_setfam_1(X10),k4_xboole_0(k1_setfam_1(X10),X8))
        | k1_xboole_0 = X10 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f78,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f96,plain,(
    ! [X17,X18] :
      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | k1_setfam_1(k2_xboole_0(X18,k2_enumset1(X17,X17,X17,X17))) = k4_xboole_0(k1_setfam_1(X18),k4_xboole_0(k1_setfam_1(X18),X17))
      | k1_xboole_0 = X18 ) ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,(
    ! [X17,X18] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | k1_setfam_1(k2_xboole_0(X18,k2_enumset1(X17,X17,X17,X17))) = k4_xboole_0(k1_setfam_1(X18),k4_xboole_0(k1_setfam_1(X18),X17))
      | k1_xboole_0 = X18 ) ),
    inference(superposition,[],[f56,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)
      | k1_setfam_1(k2_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X0))
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f39,f34])).

fof(f34,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_enumset1(X0,X0,X0,X0)
      | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(superposition,[],[f37,f54])).

% (9729)Refutation not found, incomplete strategy% (9729)------------------------------
% (9729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f54,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) ),
    inference(resolution,[],[f36,f41])).

fof(f41,plain,(
    ! [X1] : ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f29,f32,f32])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ) ),
    inference(definition_unfolding,[],[f25,f32,f24,f32,f32])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f207,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl2_3 ),
    inference(resolution,[],[f200,f190])).

fof(f190,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f41,f185])).

fof(f185,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl2_3 ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl2_3 ),
    inference(superposition,[],[f33,f148])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
        | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) )
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f127,f34])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X1))
        | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) )
    | ~ spl2_3 ),
    inference(superposition,[],[f99,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f23,f31,f32,f32])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f99,plain,
    ( ! [X10,X8] :
        ( k1_setfam_1(k2_xboole_0(X10,k2_enumset1(X8,X8,X8,X8))) = k4_xboole_0(k1_setfam_1(X10),k4_xboole_0(k1_setfam_1(X10),X8))
        | k1_xboole_0 = X10 )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f33,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f19,f24,f31])).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f200,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f56,f185])).

fof(f104,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f87,f78,f98])).

fof(f87,plain,(
    ! [X12,X11] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | k1_setfam_1(k2_xboole_0(X12,k2_enumset1(X11,X11,X11,X11))) = k4_xboole_0(k1_setfam_1(X12),k4_xboole_0(k1_setfam_1(X12),X11))
      | k1_xboole_0 = X12 ) ),
    inference(superposition,[],[f41,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:08:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (9730)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (9730)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (9720)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (9721)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (9721)Refutation not found, incomplete strategy% (9721)------------------------------
% 0.20/0.51  % (9721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9721)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9721)Memory used [KB]: 6140
% 0.20/0.51  % (9721)Time elapsed: 0.108 s
% 0.20/0.51  % (9721)------------------------------
% 0.20/0.51  % (9721)------------------------------
% 0.20/0.51  % (9729)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f104,f207,f213])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    spl2_3 | spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f96,f78,f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    spl2_3 <=> ! [X8,X10] : (k1_setfam_1(k2_xboole_0(X10,k2_enumset1(X8,X8,X8,X8))) = k4_xboole_0(k1_setfam_1(X10),k4_xboole_0(k1_setfam_1(X10),X8)) | k1_xboole_0 = X10)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl2_2 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    ( ! [X17,X18] : (r1_xboole_0(k1_xboole_0,k1_xboole_0) | k1_setfam_1(k2_xboole_0(X18,k2_enumset1(X17,X17,X17,X17))) = k4_xboole_0(k1_setfam_1(X18),k4_xboole_0(k1_setfam_1(X18),X17)) | k1_xboole_0 = X18) )),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X17,X18] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0) | k1_setfam_1(k2_xboole_0(X18,k2_enumset1(X17,X17,X17,X17))) = k4_xboole_0(k1_setfam_1(X18),k4_xboole_0(k1_setfam_1(X18),X17)) | k1_xboole_0 = X18) )),
% 0.20/0.51    inference(superposition,[],[f56,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) | k1_setfam_1(k2_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X0)) | k1_xboole_0 = X1) )),
% 0.20/0.51    inference(superposition,[],[f39,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f20,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f21,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f22,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f28,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.51    inference(superposition,[],[f37,f54])).
% 0.20/0.51  % (9729)Refutation not found, incomplete strategy% (9729)------------------------------
% 0.20/0.51  % (9729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))) )),
% 0.20/0.51    inference(resolution,[],[f36,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X1] : (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.20/0.51    inference(equality_resolution,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f29,f32,f32])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f25,f32,f24,f32,f32])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f27,f24])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    ~spl2_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f205])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    $false | ~spl2_3),
% 0.20/0.51    inference(resolution,[],[f200,f190])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_3),
% 0.20/0.51    inference(superposition,[],[f41,f185])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl2_3),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f175])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl2_3),
% 0.20/0.51    inference(superposition,[],[f33,f148])).
% 0.20/0.51  fof(f148,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) ) | ~spl2_3),
% 0.20/0.51    inference(forward_demodulation,[],[f127,f34])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X1)) | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) ) | ~spl2_3),
% 0.20/0.51    inference(superposition,[],[f99,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f23,f31,f32,f32])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ( ! [X10,X8] : (k1_setfam_1(k2_xboole_0(X10,k2_enumset1(X8,X8,X8,X8))) = k4_xboole_0(k1_setfam_1(X10),k4_xboole_0(k1_setfam_1(X10),X8)) | k1_xboole_0 = X10) ) | ~spl2_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f98])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.20/0.51    inference(definition_unfolding,[],[f19,f24,f31])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.51    inference(negated_conjecture,[],[f11])).
% 0.20/0.51  fof(f11,conjecture,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_3),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f194])).
% 0.20/0.51  fof(f194,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_3),
% 0.20/0.51    inference(superposition,[],[f56,f185])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    spl2_3 | ~spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f87,f78,f98])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X12,X11] : (~r1_xboole_0(k1_xboole_0,k1_xboole_0) | k1_setfam_1(k2_xboole_0(X12,k2_enumset1(X11,X11,X11,X11))) = k4_xboole_0(k1_setfam_1(X12),k4_xboole_0(k1_setfam_1(X12),X11)) | k1_xboole_0 = X12) )),
% 0.20/0.51    inference(superposition,[],[f41,f43])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (9730)------------------------------
% 0.20/0.51  % (9730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9730)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (9730)Memory used [KB]: 6396
% 0.20/0.51  % (9730)Time elapsed: 0.094 s
% 0.20/0.51  % (9730)------------------------------
% 0.20/0.51  % (9730)------------------------------
% 0.20/0.51  % (9729)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9729)Memory used [KB]: 10618
% 0.20/0.51  % (9729)Time elapsed: 0.076 s
% 0.20/0.51  % (9729)------------------------------
% 0.20/0.51  % (9729)------------------------------
% 0.20/0.51  % (9712)Success in time 0.149 s
%------------------------------------------------------------------------------
