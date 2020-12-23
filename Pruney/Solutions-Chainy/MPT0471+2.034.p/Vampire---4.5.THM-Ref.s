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
% DateTime   : Thu Dec  3 12:48:09 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  45 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 (  89 expanded)
%              Number of equality atoms :   40 (  47 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f30,f34,f39,f47])).

fof(f47,plain,
    ( spl0_1
    | ~ spl0_2
    | ~ spl0_3
    | ~ spl0_4 ),
    inference(avatar_split_clause,[],[f45,f37,f32,f28,f24])).

fof(f24,plain,
    ( spl0_1
  <=> k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).

fof(f28,plain,
    ( spl0_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).

fof(f32,plain,
    ( spl0_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).

fof(f37,plain,
    ( spl0_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_4])])).

fof(f45,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl0_2
    | ~ spl0_3
    | ~ spl0_4 ),
    inference(forward_demodulation,[],[f44,f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f44,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl0_2
    | ~ spl0_3
    | ~ spl0_4 ),
    inference(forward_demodulation,[],[f43,f33])).

fof(f33,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl0_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f43,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl0_2
    | ~ spl0_4 ),
    inference(forward_demodulation,[],[f42,f29])).

fof(f29,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl0_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f42,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl0_4 ),
    inference(resolution,[],[f16,f38])).

fof(f38,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl0_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f39,plain,(
    spl0_4 ),
    inference(avatar_split_clause,[],[f35,f37])).

fof(f35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f17,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f17,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f34,plain,(
    spl0_3 ),
    inference(avatar_split_clause,[],[f13,f32])).

fof(f13,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f30,plain,(
    spl0_2 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    ~ spl0_1 ),
    inference(avatar_split_clause,[],[f12,f24])).

fof(f12,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f7])).

fof(f7,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n008.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:18:00 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.42  % (27233)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.42  % (27233)Refutation not found, incomplete strategy% (27233)------------------------------
% 0.19/0.42  % (27233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (27233)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.42  
% 0.19/0.42  % (27233)Memory used [KB]: 1535
% 0.19/0.42  % (27233)Time elapsed: 0.003 s
% 0.19/0.42  % (27233)------------------------------
% 0.19/0.42  % (27233)------------------------------
% 0.19/0.45  % (27220)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.45  % (27220)Refutation not found, incomplete strategy% (27220)------------------------------
% 0.19/0.45  % (27220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (27220)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (27220)Memory used [KB]: 6012
% 0.19/0.45  % (27220)Time elapsed: 0.058 s
% 0.19/0.45  % (27220)------------------------------
% 0.19/0.45  % (27220)------------------------------
% 0.19/0.46  % (27226)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.46  % (27226)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f26,f30,f34,f39,f47])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    spl0_1 | ~spl0_2 | ~spl0_3 | ~spl0_4),
% 0.19/0.46    inference(avatar_split_clause,[],[f45,f37,f32,f28,f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    spl0_1 <=> k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    spl0_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    spl0_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    spl0_4 <=> v1_relat_1(k1_xboole_0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl0_4])])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    k1_xboole_0 = k3_relat_1(k1_xboole_0) | (~spl0_2 | ~spl0_3 | ~spl0_4)),
% 0.19/0.46    inference(forward_demodulation,[],[f44,f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.46    inference(cnf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl0_2 | ~spl0_3 | ~spl0_4)),
% 0.19/0.46    inference(forward_demodulation,[],[f43,f33])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl0_3),
% 0.19/0.46    inference(avatar_component_clause,[],[f32])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl0_2 | ~spl0_4)),
% 0.19/0.46    inference(forward_demodulation,[],[f42,f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl0_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f28])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~spl0_4),
% 0.19/0.46    inference(resolution,[],[f16,f38])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    v1_relat_1(k1_xboole_0) | ~spl0_4),
% 0.19/0.46    inference(avatar_component_clause,[],[f37])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f9])).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    spl0_4),
% 0.19/0.46    inference(avatar_split_clause,[],[f35,f37])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    v1_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(superposition,[],[f17,f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.46    inference(equality_resolution,[],[f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.46    inference(cnf_transformation,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.46    inference(flattening,[],[f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.46    inference(nnf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    spl0_3),
% 0.19/0.46    inference(avatar_split_clause,[],[f13,f32])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(cnf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    spl0_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f14,f28])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(cnf_transformation,[],[f5])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ~spl0_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f12,f24])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(cnf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,plain,(
% 0.19/0.46    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(flattening,[],[f7])).
% 0.19/0.46  fof(f7,negated_conjecture,(
% 0.19/0.46    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(negated_conjecture,[],[f6])).
% 0.19/0.46  fof(f6,conjecture,(
% 0.19/0.46    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (27226)------------------------------
% 0.19/0.46  % (27226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (27226)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (27226)Memory used [KB]: 10618
% 0.19/0.46  % (27226)Time elapsed: 0.038 s
% 0.19/0.46  % (27226)------------------------------
% 0.19/0.46  % (27226)------------------------------
% 0.19/0.46  % (27219)Success in time 0.117 s
%------------------------------------------------------------------------------
