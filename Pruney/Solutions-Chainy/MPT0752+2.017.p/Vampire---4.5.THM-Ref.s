%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 (  80 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  163 ( 226 expanded)
%              Number of equality atoms :   33 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f59,f61,f91])).

fof(f91,plain,
    ( ~ spl2_1
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl2_1
    | spl2_4 ),
    inference(subsumption_resolution,[],[f87,f52])).

fof(f52,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_4
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f87,plain,
    ( v5_ordinal1(k1_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f32,f83])).

fof(f83,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1(k1_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f78,f71])).

fof(f71,plain,(
    k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f68,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v5_ordinal1(sK1(X0))
      & v1_funct_1(sK1(X0))
      & v5_relat_1(sK1(X0),X0)
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v5_ordinal1(X1)
          & v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
     => ( v5_ordinal1(sK1(X0))
        & v1_funct_1(sK1(X0))
        & v5_relat_1(sK1(X0),X0)
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_ordinal1)).

fof(f68,plain,
    ( ~ v1_relat_1(sK1(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f62,f30])).

fof(f30,plain,(
    ! [X0] : v5_relat_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f78,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_relat_1(sK1(X1))
        | k1_xboole_0 = sK1(X1) )
    | ~ spl2_1 ),
    inference(resolution,[],[f76,f29])).

fof(f76,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(X4)
        | k1_xboole_0 != k2_relat_1(X4)
        | k1_xboole_0 = X4 )
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f75,f24])).

fof(f24,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f75,plain,
    ( ! [X4] :
        ( k1_xboole_0 != k2_relat_1(X4)
        | k1_xboole_0 != k2_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X4)
        | k1_xboole_0 = X4 )
    | ~ spl2_1 ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X1)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k2_relat_1(X1)
          | k1_xboole_0 != k2_relat_1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k2_relat_1(X1)
          | k1_xboole_0 != k2_relat_1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k1_xboole_0 = k2_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).

fof(f32,plain,(
    ! [X0] : v5_ordinal1(sK1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f54,f48])).

fof(f48,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_3
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f54,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f26,f22])).

fof(f22,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f26,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

% (13202)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f59,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f44,f34])).

fof(f34,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(f44,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_2
  <=> v5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f57,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f55,f40])).

fof(f40,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f25,f22])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f21,f50,f46,f42,f38])).

fof(f21,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ~ v5_ordinal1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
   => ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,sK0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:17:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (13186)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.48  % (13186)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (13210)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f53,f57,f59,f61,f91])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~spl2_1 | spl2_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    $false | (~spl2_1 | spl2_4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f87,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ~v5_ordinal1(k1_xboole_0) | spl2_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl2_4 <=> v5_ordinal1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    v5_ordinal1(k1_xboole_0) | ~spl2_1),
% 0.22/0.49    inference(superposition,[],[f32,f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    k1_xboole_0 = sK1(k1_xboole_0) | ~spl2_1),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1(k1_xboole_0) | ~spl2_1),
% 0.22/0.49    inference(superposition,[],[f78,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f68,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (v5_ordinal1(sK1(X0)) & v1_funct_1(sK1(X0)) & v5_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v5_ordinal1(sK1(X0)) & v1_funct_1(sK1(X0)) & v5_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ? [X1] : (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_ordinal1)).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ~v1_relat_1(sK1(k1_xboole_0)) | k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0))),
% 0.22/0.49    inference(resolution,[],[f62,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0] : (v5_relat_1(sK1(X0),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X0] : (~v5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 0.22/0.49    inference(resolution,[],[f35,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X1] : (k1_xboole_0 != k2_relat_1(sK1(X1)) | k1_xboole_0 = sK1(X1)) ) | ~spl2_1),
% 0.22/0.49    inference(resolution,[],[f76,f29])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X4] : (~v1_relat_1(X4) | k1_xboole_0 != k2_relat_1(X4) | k1_xboole_0 = X4) ) | ~spl2_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f75,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X4] : (k1_xboole_0 != k2_relat_1(X4) | k1_xboole_0 != k2_relat_1(k1_xboole_0) | ~v1_relat_1(X4) | k1_xboole_0 = X4) ) | ~spl2_1),
% 0.22/0.49    inference(resolution,[],[f27,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    v1_relat_1(k1_xboole_0) | ~spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl2_1 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X1) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X1) | X0 = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (X0 = X1 | k1_xboole_0 != k2_relat_1(X1) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((X0 = X1 | (k1_xboole_0 != k2_relat_1(X1) | k1_xboole_0 != k2_relat_1(X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0] : (v5_ordinal1(sK1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl2_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    $false | spl2_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f54,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ~v1_funct_1(k1_xboole_0) | spl2_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl2_3 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    v1_funct_1(k1_xboole_0)),
% 0.22/0.49    inference(superposition,[],[f26,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.49  % (13202)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl2_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    $false | spl2_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f44,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ~v5_relat_1(k1_xboole_0,sK0) | spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    spl2_2 <=> v5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl2_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    $false | spl2_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f55,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ~v1_relat_1(k1_xboole_0) | spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f38])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    v1_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(superposition,[],[f25,f22])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f21,f50,f46,f42,f38])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) => (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (13186)------------------------------
% 0.22/0.49  % (13186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13186)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (13186)Memory used [KB]: 10746
% 0.22/0.49  % (13186)Time elapsed: 0.090 s
% 0.22/0.49  % (13186)------------------------------
% 0.22/0.49  % (13186)------------------------------
% 0.22/0.49  % (13182)Success in time 0.13 s
%------------------------------------------------------------------------------
