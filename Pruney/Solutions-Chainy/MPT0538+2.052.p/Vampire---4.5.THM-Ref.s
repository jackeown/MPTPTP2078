%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 103 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 245 expanded)
%              Number of equality atoms :   50 ( 135 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f43,f48,f82,f86])).

fof(f86,plain,
    ( spl1_1
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl1_1
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(subsumption_resolution,[],[f69,f78])).

fof(f78,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl1_6
  <=> ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f69,plain,
    ( ! [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
    | spl1_1
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(superposition,[],[f30,f55])).

fof(f55,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k1_xboole_0) = k8_relat_1(X1,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(superposition,[],[f54,f54])).

fof(f54,plain,
    ( ! [X2] : k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f53,f27])).

fof(f27,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f53,plain,
    ( ! [X2] : k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X2))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f52,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f52,plain,
    ( ! [X2] : k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),X2))
    | ~ spl1_5 ),
    inference(resolution,[],[f22,f47])).

fof(f47,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl1_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(f30,plain,
    ( k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f82,plain,
    ( ~ spl1_5
    | spl1_6
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f73,f46,f41,f77,f46])).

fof(f73,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k8_relat_1(X1,k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(superposition,[],[f21,f55])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f48,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f44,f33,f46])).

fof(f33,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f44,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(superposition,[],[f20,f34])).

fof(f34,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f43,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f35,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f31,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f16,f29])).

fof(f16,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (18841)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.44  % (18849)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.46  % (18846)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (18846)Refutation not found, incomplete strategy% (18846)------------------------------
% 0.20/0.46  % (18846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18847)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (18838)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (18846)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (18846)Memory used [KB]: 1535
% 0.20/0.47  % (18846)Time elapsed: 0.053 s
% 0.20/0.47  % (18846)------------------------------
% 0.20/0.47  % (18846)------------------------------
% 0.20/0.48  % (18839)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (18839)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f31,f35,f43,f48,f82,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl1_1 | ~spl1_4 | ~spl1_5 | ~spl1_6),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    $false | (spl1_1 | ~spl1_4 | ~spl1_5 | ~spl1_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f69,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | ~spl1_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl1_6 <=> ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)) ) | (spl1_1 | ~spl1_4 | ~spl1_5)),
% 0.20/0.49    inference(superposition,[],[f30,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_relat_1(X0,k1_xboole_0) = k8_relat_1(X1,k1_xboole_0)) ) | (~spl1_4 | ~spl1_5)),
% 0.20/0.49    inference(superposition,[],[f54,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X2] : (k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0)) ) | (~spl1_4 | ~spl1_5)),
% 0.20/0.49    inference(forward_demodulation,[],[f53,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X2] : (k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,X2))) ) | (~spl1_4 | ~spl1_5)),
% 0.20/0.49    inference(forward_demodulation,[],[f52,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X2] : (k8_relat_1(X2,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),X2))) ) | ~spl1_5),
% 0.20/0.49    inference(resolution,[],[f22,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    v1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    spl1_5 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    spl1_1 <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ~spl1_5 | spl1_6 | ~spl1_4 | ~spl1_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f73,f46,f41,f77,f46])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k8_relat_1(X1,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_4 | ~spl1_5)),
% 0.20/0.49    inference(superposition,[],[f21,f55])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    spl1_5 | ~spl1_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f33,f46])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    v1_relat_1(k1_xboole_0) | ~spl1_2),
% 0.20/0.49    inference(superposition,[],[f20,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f33])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    spl1_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f18,f41])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    spl1_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f17,f33])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ~spl1_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f16,f29])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 0.20/0.49  fof(f12,plain,(
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
% 0.20/0.49  % (18839)------------------------------
% 0.20/0.49  % (18839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18839)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (18839)Memory used [KB]: 10618
% 0.20/0.49  % (18839)Time elapsed: 0.005 s
% 0.20/0.49  % (18839)------------------------------
% 0.20/0.49  % (18839)------------------------------
% 0.20/0.49  % (18832)Success in time 0.132 s
%------------------------------------------------------------------------------
