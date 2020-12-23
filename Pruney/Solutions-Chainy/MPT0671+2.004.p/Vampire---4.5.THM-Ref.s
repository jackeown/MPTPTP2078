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
% DateTime   : Thu Dec  3 12:53:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  65 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :  112 ( 169 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f33,f41,f45,f49,f55,f67,f75])).

fof(f75,plain,
    ( spl2_1
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl2_1
    | ~ spl2_10 ),
    inference(resolution,[],[f66,f22])).

fof(f22,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl2_1
  <=> r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f66,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_10
  <=> ! [X0] : r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f67,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f63,f53,f43,f39,f30,f65])).

fof(f30,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f39,plain,
    ( spl2_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f43,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f53,plain,
    ( spl2_8
  <=> ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f63,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1))
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f62,f32])).

fof(f32,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f62,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f60,f40])).

fof(f40,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f60,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(superposition,[],[f44,f54])).

fof(f54,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f55,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f50,f47,f30,f53])).

fof(f47,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f50,plain,
    ( ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f48,f32])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f49,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f18,f47])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f45,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f41,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f33,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_funct_1)).

fof(f23,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f14,f20])).

fof(f14,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:57:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (3380)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.41  % (3383)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.42  % (3378)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (3379)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (3379)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f23,f33,f41,f45,f49,f55,f67,f75])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl2_1 | ~spl2_10),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f74])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    $false | (spl2_1 | ~spl2_10)),
% 0.21/0.43    inference(resolution,[],[f66,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) | spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    spl2_1 <=> r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1))) ) | ~spl2_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f65])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl2_10 <=> ! [X0] : r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    spl2_10 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f63,f53,f43,f39,f30,f65])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl2_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl2_6 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl2_8 <=> ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1))) ) | (~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_8)),
% 0.21/0.43    inference(subsumption_resolution,[],[f62,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    v1_relat_1(sK1) | ~spl2_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f30])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl2_5 | ~spl2_6 | ~spl2_8)),
% 0.21/0.43    inference(subsumption_resolution,[],[f60,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f39])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(sK1)) ) | (~spl2_6 | ~spl2_8)),
% 0.21/0.43    inference(superposition,[],[f44,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X0] : (k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))) ) | ~spl2_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f53])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f43])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl2_8 | ~spl2_3 | ~spl2_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f50,f47,f30,f53])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl2_7 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X0] : (k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_7)),
% 0.21/0.43    inference(resolution,[],[f48,f32])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f47])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl2_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f47])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl2_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f43])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl2_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f15,f39])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl2_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f12,f30])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    v1_relat_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ? [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.21/0.43    inference(negated_conjecture,[],[f4])).
% 0.21/0.43  fof(f4,conjecture,(
% 0.21/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_funct_1)).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ~spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f14,f20])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (3379)------------------------------
% 0.21/0.43  % (3379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (3379)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (3379)Memory used [KB]: 10490
% 0.21/0.43  % (3379)Time elapsed: 0.005 s
% 0.21/0.43  % (3379)------------------------------
% 0.21/0.43  % (3379)------------------------------
% 0.21/0.43  % (3373)Success in time 0.078 s
%------------------------------------------------------------------------------
