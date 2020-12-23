%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  78 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :  147 ( 258 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f50,f54,f62,f67])).

fof(f67,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f26,f65])).

fof(f65,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f58,f63])).

fof(f63,plain,
    ( k1_tarski(k1_funct_1(sK1,sK0)) = k11_relat_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f26,f31,f36,f61])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f36,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_3
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f31,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f58,plain,
    ( k1_tarski(k1_funct_1(sK1,sK0)) != k11_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_1
    | spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f57,f55])).

fof(f55,plain,
    ( ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f26,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f57,plain,
    ( k1_tarski(k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f41,f53])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f41,plain,
    ( k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_4
  <=> k1_tarski(k1_funct_1(sK1,sK0)) = k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f26,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f62,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f22,f60])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f54,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f50,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f42,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

fof(f37,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f29])).

fof(f16,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f15,f24])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (11842)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (11842)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (11849)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f50,f54,f62,f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_8),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f66])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_8)),
% 0.20/0.46    inference(subsumption_resolution,[],[f26,f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ~v1_relat_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_8)),
% 0.20/0.46    inference(subsumption_resolution,[],[f58,f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    k1_tarski(k1_funct_1(sK1,sK0)) = k11_relat_1(sK1,sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_8)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f26,f31,f36,f61])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl2_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    spl2_8 <=> ! [X1,X0] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    spl2_3 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    v1_funct_1(sK1) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    spl2_2 <=> v1_funct_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    k1_tarski(k1_funct_1(sK1,sK0)) != k11_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | (~spl2_1 | spl2_4 | ~spl2_6 | ~spl2_7)),
% 0.20/0.46    inference(forward_demodulation,[],[f57,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0))) ) | (~spl2_1 | ~spl2_6)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f26,f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl2_6 <=> ! [X1,X0] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    k1_tarski(k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k1_tarski(sK0)) | ~v1_relat_1(sK1) | (spl2_4 | ~spl2_7)),
% 0.20/0.46    inference(superposition,[],[f41,f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl2_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    spl2_7 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) | spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl2_4 <=> k1_tarski(k1_funct_1(sK1,sK0)) = k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    spl2_1 <=> v1_relat_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    spl2_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f60])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    spl2_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f52])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    spl2_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f48])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ~spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f18,f39])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f17,f34])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f16,f29])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    v1_funct_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f15,f24])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (11842)------------------------------
% 0.20/0.46  % (11842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (11842)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (11842)Memory used [KB]: 6140
% 0.20/0.46  % (11842)Time elapsed: 0.049 s
% 0.20/0.46  % (11842)------------------------------
% 0.20/0.46  % (11842)------------------------------
% 0.20/0.46  % (11836)Success in time 0.101 s
%------------------------------------------------------------------------------
