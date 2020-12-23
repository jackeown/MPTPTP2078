%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  45 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 (  96 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f40,f42,f45,f48])).

fof(f48,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl1_4 ),
    inference(unit_resulting_resolution,[],[f15,f36,f18])).

fof(f18,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v5_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).

fof(f36,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl1_4
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f15,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f45,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f44])).

fof(f44,plain,
    ( $false
    | spl1_3 ),
    inference(unit_resulting_resolution,[],[f15,f32,f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f32,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl1_3
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f42,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | spl1_2 ),
    inference(unit_resulting_resolution,[],[f20,f28])).

fof(f28,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl1_2
  <=> v5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f20,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(f40,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f39])).

fof(f39,plain,
    ( $false
    | spl1_1 ),
    inference(unit_resulting_resolution,[],[f15,f24,f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f24,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl1_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f37,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f14,f34,f30,f26,f22])).

fof(f14,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).

fof(f12,plain,
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

fof(f8,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:59:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.41  % (7826)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.46  % (7826)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f37,f40,f42,f45,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl1_4),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    $false | spl1_4),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f15,f36,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => v5_ordinal1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ~v5_ordinal1(k1_xboole_0) | spl1_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl1_4 <=> v5_ordinal1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    spl1_3),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    $false | spl1_3),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f15,f32,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ~v1_funct_1(k1_xboole_0) | spl1_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    spl1_3 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl1_2),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    $false | spl1_2),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f20,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ~v5_relat_1(k1_xboole_0,sK0) | spl1_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    spl1_2 <=> v5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    spl1_1),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    $false | spl1_1),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f15,f24,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ~v1_relat_1(k1_xboole_0) | spl1_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    spl1_1 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ~spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f14,f34,f30,f26,f22])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) => (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.46    inference(negated_conjecture,[],[f6])).
% 0.21/0.46  fof(f6,conjecture,(
% 0.21/0.46    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (7826)------------------------------
% 0.21/0.46  % (7826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (7826)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (7826)Memory used [KB]: 5373
% 0.21/0.46  % (7826)Time elapsed: 0.057 s
% 0.21/0.46  % (7826)------------------------------
% 0.21/0.46  % (7826)------------------------------
% 0.21/0.47  % (7812)Success in time 0.11 s
%------------------------------------------------------------------------------
