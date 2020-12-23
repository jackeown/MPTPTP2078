%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  81 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 277 expanded)
%              Number of equality atoms :   31 ( 108 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f31,f34])).

fof(f34,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f33])).

fof(f33,plain,
    ( $false
    | spl1_2 ),
    inference(subsumption_resolution,[],[f32,f24])).

fof(f24,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f14,f11])).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0))
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0))
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
            & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f32,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | spl1_2 ),
    inference(forward_demodulation,[],[f22,f28])).

fof(f28,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f27,f11])).

fof(f27,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f26,f12])).

fof(f12,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f26,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f16,f13])).

fof(f13,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f22,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f31,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f30])).

fof(f30,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f29,f25])).

fof(f25,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f15,f11])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0))
    | spl1_1 ),
    inference(superposition,[],[f19,f28])).

fof(f19,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f23,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f10,f21,f18])).

fof(f10,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:48:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (23894)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.45  % (23891)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.45  % (23895)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.45  % (23891)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f23,f31,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl1_2),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    $false | spl1_2),
% 0.21/0.46    inference(subsumption_resolution,[],[f32,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.46    inference(resolution,[],[f14,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    v1_relat_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0)) | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f5])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0)) | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f3])).
% 0.21/0.46  fof(f3,conjecture,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | spl1_2),
% 0.21/0.46    inference(forward_demodulation,[],[f22,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f27,f11])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f26,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    v1_funct_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.46    inference(resolution,[],[f16,f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    v2_funct_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | spl1_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    spl1_2 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    spl1_1),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    $false | spl1_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f29,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.21/0.46    inference(resolution,[],[f15,f11])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0)) | spl1_1),
% 0.21/0.46    inference(superposition,[],[f19,f28])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | spl1_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    spl1_1 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ~spl1_1 | ~spl1_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f10,f21,f18])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (23891)------------------------------
% 0.21/0.46  % (23891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (23891)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (23891)Memory used [KB]: 10490
% 0.21/0.46  % (23891)Time elapsed: 0.035 s
% 0.21/0.46  % (23891)------------------------------
% 0.21/0.46  % (23891)------------------------------
% 0.21/0.46  % (23887)Success in time 0.104 s
%------------------------------------------------------------------------------
