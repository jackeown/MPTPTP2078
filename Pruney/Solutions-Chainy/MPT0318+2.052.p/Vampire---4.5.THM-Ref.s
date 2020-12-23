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
% DateTime   : Thu Dec  3 12:42:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 123 expanded)
%              Number of leaves         :   14 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 197 expanded)
%              Number of equality atoms :   72 ( 153 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f61,f68,f85,f86,f90])).

fof(f90,plain,
    ( spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f51,f56,f66,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f66,plain,
    ( k1_xboole_0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_4
  <=> k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f56,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f51,plain,
    ( k1_xboole_0 != sK0
    | spl2_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f76,f65,f82])).

fof(f82,plain,
    ( spl2_5
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f76,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl2_4 ),
    inference(superposition,[],[f47,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f47,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f25,f17,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f16,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f23,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f16,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f85,plain,
    ( ~ spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f74,f65,f82])).

fof(f74,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl2_4 ),
    inference(superposition,[],[f43,f67])).

fof(f43,plain,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) != k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k3_enumset1(X0,X0,X0,X0,X0) != k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f22,f32,f17,f32,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f15,f31])).

fof(f15,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

% (23305)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f68,plain,
    ( spl2_4
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f63,f58,f49,f65])).

fof(f58,plain,
    ( spl2_3
  <=> k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f63,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_3 ),
    inference(trivial_inequality_removal,[],[f62])).

fof(f62,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_3 ),
    inference(superposition,[],[f18,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f61,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f33,f58,f54])).

fof(f33,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f13,f32,f32])).

fof(f13,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f52,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f14,f49])).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (23304)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (23316)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (23324)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (23309)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (23324)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f52,f61,f68,f85,f86,f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    spl2_1 | ~spl2_2 | spl2_4),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    $false | (spl2_1 | ~spl2_2 | spl2_4)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f51,f56,f66,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    k1_xboole_0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | spl2_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    spl2_4 <=> k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl2_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    spl2_2 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    k1_xboole_0 != sK0 | spl2_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    spl2_1 <=> k1_xboole_0 = sK0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    spl2_5 | ~spl2_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f76,f65,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    spl2_5 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl2_4),
% 0.20/0.52    inference(superposition,[],[f47,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl2_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f65])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 0.20/0.52    inference(equality_resolution,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f25,f17,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f16,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f23,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ~spl2_5 | ~spl2_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f74,f65,f82])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl2_4),
% 0.20/0.52    inference(superposition,[],[f43,f67])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X1] : (k3_enumset1(X1,X1,X1,X1,X1) != k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)))) )),
% 0.20/0.52    inference(equality_resolution,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (X0 != X1 | k3_enumset1(X0,X0,X0,X0,X0) != k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f22,f32,f17,f32,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f15,f31])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  % (23305)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    spl2_4 | spl2_1 | ~spl2_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f63,f58,f49,f65])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    spl2_3 <=> k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl2_3),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl2_3),
% 0.20/0.53    inference(superposition,[],[f18,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | ~spl2_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f58])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    spl2_2 | spl2_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f33,f58,f54])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    k1_xboole_0 = k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.53    inference(definition_unfolding,[],[f13,f32,f32])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.53    inference(negated_conjecture,[],[f9])).
% 0.20/0.53  fof(f9,conjecture,(
% 0.20/0.53    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ~spl2_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f14,f49])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    k1_xboole_0 != sK0),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (23324)------------------------------
% 0.20/0.53  % (23324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23324)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (23324)Memory used [KB]: 10746
% 0.20/0.53  % (23324)Time elapsed: 0.060 s
% 0.20/0.53  % (23324)------------------------------
% 0.20/0.53  % (23324)------------------------------
% 0.20/0.53  % (23297)Success in time 0.168 s
%------------------------------------------------------------------------------
