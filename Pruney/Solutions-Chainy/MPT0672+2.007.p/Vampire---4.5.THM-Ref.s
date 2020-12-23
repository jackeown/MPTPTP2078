%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  77 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :  142 ( 259 expanded)
%              Number of equality atoms :   39 (  76 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f42,f46,f50,f55,f59,f64,f67])).

fof(f67,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f26,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_2
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X1,sK2)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f64,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f60,f48,f39,f62])).

fof(f39,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f48,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X1,sK2)) )
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f49,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f59,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f56,f53,f29,f20])).

fof(f20,plain,
    ( spl3_1
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f53,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f56,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f54,f31])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f55,plain,
    ( spl3_8
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f51,f44,f39,f53])).

fof(f44,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(resolution,[],[f45,f41])).

fof(f45,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f50,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f18,f48])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

fof(f46,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f42,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f13,f39])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
      | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
    & r1_tarski(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
          | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
        & r1_tarski(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
        | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
      & r1_tarski(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

% (27352)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
          & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

fof(f32,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f16,f24,f20])).

fof(f16,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (27350)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.44  % (27350)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f27,f32,f42,f46,f50,f55,f59,f64,f67])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    spl3_2 | ~spl3_3 | ~spl3_9),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f66])).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    $false | (spl3_2 | ~spl3_3 | ~spl3_9)),
% 0.20/0.44    inference(subsumption_resolution,[],[f65,f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | spl3_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    spl3_2 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | (~spl3_3 | ~spl3_9)),
% 0.20/0.44    inference(resolution,[],[f63,f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X1,sK2))) ) | ~spl3_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f62])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    spl3_9 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X1,sK2)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    spl3_9 | ~spl3_5 | ~spl3_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f60,f48,f39,f62])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    spl3_5 <=> v1_relat_1(sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    spl3_7 <=> ! [X1,X0,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X1,sK2))) ) | (~spl3_5 | ~spl3_7)),
% 0.20/0.45    inference(resolution,[],[f49,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    v1_relat_1(sK2) | ~spl3_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f39])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))) ) | ~spl3_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f48])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    spl3_1 | ~spl3_3 | ~spl3_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f56,f53,f29,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    spl3_1 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    spl3_8 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | (~spl3_3 | ~spl3_8)),
% 0.20/0.45    inference(resolution,[],[f54,f31])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))) ) | ~spl3_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f53])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    spl3_8 | ~spl3_5 | ~spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f51,f44,f39,f53])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    spl3_6 <=> ! [X1,X0,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))) ) | (~spl3_5 | ~spl3_6)),
% 0.20/0.45    inference(resolution,[],[f45,f41])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))) ) | ~spl3_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f44])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    spl3_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f18,f48])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.45    inference(flattening,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f17,f44])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.45    inference(flattening,[],[f7])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    spl3_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f13,f39])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    v1_relat_1(sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    (k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => ((k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f6,plain,(
% 0.20/0.45    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.45    inference(flattening,[],[f5])).
% 0.20/0.45  fof(f5,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  % (27352)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.45  fof(f4,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.20/0.45    inference(negated_conjecture,[],[f3])).
% 0.20/0.45  fof(f3,conjecture,(
% 0.20/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f15,f29])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    r1_tarski(sK0,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ~spl3_1 | ~spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f16,f24,f20])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (27350)------------------------------
% 0.20/0.45  % (27350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (27350)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (27350)Memory used [KB]: 10618
% 0.20/0.45  % (27350)Time elapsed: 0.007 s
% 0.20/0.45  % (27350)------------------------------
% 0.20/0.45  % (27350)------------------------------
% 0.20/0.45  % (27344)Success in time 0.097 s
%------------------------------------------------------------------------------
