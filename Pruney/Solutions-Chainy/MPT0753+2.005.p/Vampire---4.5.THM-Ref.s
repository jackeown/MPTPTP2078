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
% DateTime   : Thu Dec  3 12:55:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  66 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 264 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f33,f42])).

fof(f42,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | spl1_2 ),
    inference(subsumption_resolution,[],[f40,f29])).

fof(f29,plain,
    ( ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl1_2
  <=> v5_relat_1(sK0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f40,plain,(
    v5_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(resolution,[],[f37,f38])).

fof(f38,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(superposition,[],[f36,f35])).

fof(f35,plain,(
    sK0 = k8_relat_1(k2_relat_1(sK0),sK0) ),
    inference(resolution,[],[f16,f13])).

fof(f13,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v3_ordinal1(k1_relat_1(X0))
         => ( v5_ordinal1(X0)
            & v1_funct_1(X0)
            & v5_relat_1(X0,k2_relat_1(X0))
            & v1_relat_1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v3_ordinal1(k1_relat_1(X0))
       => ( v5_ordinal1(X0)
          & v1_funct_1(X0)
          & v5_relat_1(X0,k2_relat_1(X0))
          & v1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_ordinal1)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK0)),X0) ),
    inference(resolution,[],[f19,f13])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | v5_relat_1(sK0,X0) ) ),
    inference(resolution,[],[f20,f13])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f33,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f32])).

fof(f32,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f31,f26])).

fof(f26,plain,
    ( ~ v5_ordinal1(sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl1_1
  <=> v5_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f31,plain,(
    v5_ordinal1(sK0) ),
    inference(resolution,[],[f17,f15])).

fof(f15,plain,(
    v3_ordinal1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(k1_relat_1(X0))
      | v5_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v5_ordinal1(X0)
    <=> v3_ordinal1(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_ordinal1)).

fof(f30,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f23,f28,f25])).

fof(f23,plain,
    ( ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | ~ v5_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f22,f14])).

fof(f14,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f22,plain,
    ( ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v5_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f12,f13])).

fof(f12,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v5_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:06:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (4857)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (4853)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.43  % (4853)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f30,f33,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl1_2),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    $false | spl1_2),
% 0.22/0.43    inference(subsumption_resolution,[],[f40,f29])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ~v5_relat_1(sK0,k2_relat_1(sK0)) | spl1_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    spl1_2 <=> v5_relat_1(sK0,k2_relat_1(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    v5_relat_1(sK0,k2_relat_1(sK0))),
% 0.22/0.43    inference(resolution,[],[f37,f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.43    inference(superposition,[],[f36,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    sK0 = k8_relat_1(k2_relat_1(sK0),sK0)),
% 0.22/0.43    inference(resolution,[],[f16,f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    v1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0] : ((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0] : (((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,negated_conjecture,(
% 0.22/0.43    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v3_ordinal1(k1_relat_1(X0)) => (v5_ordinal1(X0) & v1_funct_1(X0) & v5_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))))),
% 0.22/0.43    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v3_ordinal1(k1_relat_1(X0)) => (v5_ordinal1(X0) & v1_funct_1(X0) & v5_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_ordinal1)).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK0)),X0)) )),
% 0.22/0.43    inference(resolution,[],[f19,f13])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | v5_relat_1(sK0,X0)) )),
% 0.22/0.43    inference(resolution,[],[f20,f13])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    spl1_1),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    $false | spl1_1),
% 0.22/0.43    inference(subsumption_resolution,[],[f31,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ~v5_ordinal1(sK0) | spl1_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    spl1_1 <=> v5_ordinal1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    v5_ordinal1(sK0)),
% 0.22/0.43    inference(resolution,[],[f17,f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    v3_ordinal1(k1_relat_1(sK0))),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0] : (~v3_ordinal1(k1_relat_1(X0)) | v5_ordinal1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : (v5_ordinal1(X0) <=> v3_ordinal1(k1_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_ordinal1)).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ~spl1_1 | ~spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f28,f25])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v5_ordinal1(sK0)),
% 0.22/0.43    inference(subsumption_resolution,[],[f22,f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    v1_funct_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v5_ordinal1(sK0)),
% 0.22/0.43    inference(subsumption_resolution,[],[f12,f13])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ~v1_relat_1(sK0) | ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v5_ordinal1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (4853)------------------------------
% 0.22/0.43  % (4853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (4853)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (4853)Memory used [KB]: 10490
% 0.22/0.43  % (4853)Time elapsed: 0.006 s
% 0.22/0.43  % (4853)------------------------------
% 0.22/0.43  % (4853)------------------------------
% 0.22/0.43  % (4849)Success in time 0.067 s
%------------------------------------------------------------------------------
