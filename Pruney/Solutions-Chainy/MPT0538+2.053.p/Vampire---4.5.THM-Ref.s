%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  47 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 (  92 expanded)
%              Number of equality atoms :   45 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f34,f42,f47,f56])).

fof(f56,plain,
    ( spl1_1
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | spl1_1
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f29,f54])).

fof(f54,plain,
    ( ! [X2] : k1_xboole_0 = k8_relat_1(X2,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f53,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f53,plain,
    ( ! [X2] : k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f52,f26])).

fof(f26,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f52,plain,
    ( ! [X2] : k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X2))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f51,f41])).

fof(f41,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f51,plain,
    ( ! [X2] : k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),X2))
    | ~ spl1_5 ),
    inference(resolution,[],[f21,f46])).

fof(f46,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl1_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(f29,plain,
    ( k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f47,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f43,f32,f45])).

fof(f32,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f43,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(superposition,[],[f19,f33])).

fof(f33,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f42,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f34,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f30,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f11])).

fof(f11,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (15827)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (15835)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (15824)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.46  % (15824)Refutation not found, incomplete strategy% (15824)------------------------------
% 0.20/0.46  % (15824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (15824)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (15824)Memory used [KB]: 1535
% 0.20/0.46  % (15824)Time elapsed: 0.052 s
% 0.20/0.46  % (15824)------------------------------
% 0.20/0.46  % (15824)------------------------------
% 0.20/0.46  % (15832)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (15826)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (15821)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (15834)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (15821)Refutation not found, incomplete strategy% (15821)------------------------------
% 0.20/0.49  % (15821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15821)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15821)Memory used [KB]: 10490
% 0.20/0.49  % (15821)Time elapsed: 0.043 s
% 0.20/0.49  % (15821)------------------------------
% 0.20/0.49  % (15821)------------------------------
% 0.20/0.49  % (15831)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (15826)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f30,f34,f42,f47,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl1_1 | ~spl1_4 | ~spl1_5),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    $false | (spl1_1 | ~spl1_4 | ~spl1_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f29,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X2] : (k1_xboole_0 = k8_relat_1(X2,k1_xboole_0)) ) | (~spl1_4 | ~spl1_5)),
% 0.20/0.49    inference(forward_demodulation,[],[f53,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X2] : (k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0)) ) | (~spl1_4 | ~spl1_5)),
% 0.20/0.49    inference(forward_demodulation,[],[f52,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X2] : (k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X2))) ) | (~spl1_4 | ~spl1_5)),
% 0.20/0.49    inference(forward_demodulation,[],[f51,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X2] : (k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),X2))) ) | ~spl1_5),
% 0.20/0.49    inference(resolution,[],[f21,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    v1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    spl1_5 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    spl1_1 <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    spl1_5 | ~spl1_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f32,f45])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    v1_relat_1(k1_xboole_0) | ~spl1_2),
% 0.20/0.49    inference(superposition,[],[f19,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f32])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    spl1_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f17,f40])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    spl1_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f16,f32])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ~spl1_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f15,f28])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,negated_conjecture,(
% 0.20/0.49    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.20/0.49    inference(negated_conjecture,[],[f7])).
% 0.20/0.49  fof(f7,conjecture,(
% 0.20/0.49    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (15826)------------------------------
% 0.20/0.49  % (15826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15826)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (15826)Memory used [KB]: 10618
% 0.20/0.49  % (15826)Time elapsed: 0.029 s
% 0.20/0.49  % (15826)------------------------------
% 0.20/0.49  % (15826)------------------------------
% 0.20/0.49  % (15819)Success in time 0.137 s
%------------------------------------------------------------------------------
