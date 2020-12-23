%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  72 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 221 expanded)
%              Number of equality atoms :   47 (  94 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f37,f41,f49,f65])).

fof(f65,plain,
    ( ~ spl2_4
    | spl2_3
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f63,f47,f27,f35,f39])).

fof(f39,plain,
    ( spl2_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f35,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f27,plain,
    ( spl2_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,
    ( spl2_5
  <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f63,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_relat_1(sK1)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f62,f48])).

fof(f48,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f62,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f43,f28])).

fof(f28,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X0,X1)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f23,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X0,X1)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_relat_1(X0) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( k1_relat_1(X0) = k1_xboole_0
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f49,plain,
    ( ~ spl2_4
    | spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f44,f31,f47,f39])).

fof(f31,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f44,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f25,f32])).

fof(f32,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f41,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) = k1_xboole_0
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK1,sK0)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k9_relat_1(X1,X0) = k1_xboole_0
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k9_relat_1(X1,X0) = k1_xboole_0
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f37,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f31])).

fof(f19,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f27])).

fof(f20,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:44:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (1907)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (1908)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (1908)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f29,f33,f37,f41,f49,f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ~spl2_4 | spl2_3 | ~spl2_1 | ~spl2_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f63,f47,f27,f35,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl2_4 <=> v1_relat_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    spl2_3 <=> k1_xboole_0 = sK0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    spl2_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    spl2_5 <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    k1_xboole_0 = sK0 | ~v1_relat_1(sK1) | (~spl2_1 | ~spl2_5)),
% 0.20/0.46    inference(forward_demodulation,[],[f62,f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f47])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f61])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.46    inference(superposition,[],[f43,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f27])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X0,X1) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(global_subsumption,[],[f23,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X0,X1) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(superposition,[],[f22,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0 | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : (((k1_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ~spl2_4 | spl2_5 | ~spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f44,f31,f47,f39])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.46    inference(resolution,[],[f25,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f31])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f17,f39])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X0,X1] : (k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1] : (k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0,X1] : ((k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (v1_relat_1(X1) => ~(k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => ~(k9_relat_1(X1,X0) = k1_xboole_0 & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ~spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f18,f35])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    k1_xboole_0 != sK0),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f31])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f27])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (1908)------------------------------
% 0.20/0.46  % (1908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (1908)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (1908)Memory used [KB]: 10618
% 0.20/0.46  % (1908)Time elapsed: 0.054 s
% 0.20/0.46  % (1908)------------------------------
% 0.20/0.46  % (1908)------------------------------
% 0.20/0.46  % (1918)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.46  % (1901)Success in time 0.113 s
%------------------------------------------------------------------------------
