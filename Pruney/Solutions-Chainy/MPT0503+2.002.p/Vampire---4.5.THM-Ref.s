%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  62 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :  110 ( 156 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f31,f35,f39,f45,f51,f60])).

fof(f60,plain,
    ( spl2_1
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl2_1
    | ~ spl2_7 ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0)
    | spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f21,f50])).

fof(f50,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_7
  <=> ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f21,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl2_1
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f51,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f46,f43,f24,f49])).

fof(f24,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f43,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f46,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),X0)
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f44,f26])).

fof(f26,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f45,plain,
    ( spl2_6
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f41,f37,f33,f29,f43])).

fof(f29,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f33,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f37,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f40,f30])).

fof(f30,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1)
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(resolution,[],[f38,f34])).

fof(f34,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f38,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f39,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f35,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f31,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f27,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f13,f24])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(k7_relat_1(X1,X0),X0)
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(k7_relat_1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).

fof(f22,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f14,f19])).

fof(f14,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (21357)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (21360)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (21361)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.43  % (21361)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f22,f27,f31,f35,f39,f45,f51,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl2_1 | ~spl2_7),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f59])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    $false | (spl2_1 | ~spl2_7)),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) | (spl2_1 | ~spl2_7)),
% 0.20/0.43    inference(superposition,[],[f21,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),X0)) ) | ~spl2_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f49])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    spl2_7 <=> ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),sK0) | spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    spl2_1 <=> k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    spl2_7 | ~spl2_2 | ~spl2_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f46,f43,f24,f49])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    spl2_2 <=> v1_relat_1(sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    spl2_6 <=> ! [X1,X0] : (k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),X0)) ) | (~spl2_2 | ~spl2_6)),
% 0.20/0.43    inference(resolution,[],[f44,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f24])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1)) ) | ~spl2_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f43])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    spl2_6 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f41,f37,f33,f29,f43])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    spl2_3 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    spl2_4 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    spl2_5 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.20/0.43    inference(subsumption_resolution,[],[f40,f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f29])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl2_4 | ~spl2_5)),
% 0.20/0.43    inference(resolution,[],[f38,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl2_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f33])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl2_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f37])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    spl2_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f17,f37])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    spl2_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f16,f33])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    spl2_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f15,f29])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f13,f24])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    v1_relat_1(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),sK0) & v1_relat_1(sK1)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(k7_relat_1(X1,X0),X0) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),sK0) & v1_relat_1(sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(k7_relat_1(X1,X0),X0) & v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0))),
% 0.20/0.43    inference(negated_conjecture,[],[f4])).
% 0.20/0.43  fof(f4,conjecture,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ~spl2_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f14,f19])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (21361)------------------------------
% 0.20/0.43  % (21361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (21361)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (21361)Memory used [KB]: 6012
% 0.20/0.43  % (21361)Time elapsed: 0.027 s
% 0.20/0.43  % (21361)------------------------------
% 0.20/0.43  % (21361)------------------------------
% 0.20/0.43  % (21350)Success in time 0.075 s
%------------------------------------------------------------------------------
