%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 (  89 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :  139 ( 193 expanded)
%              Number of equality atoms :   40 (  54 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f43,f47,f51,f55,f60,f66,f72,f78,f90,f93])).

fof(f93,plain,
    ( spl2_1
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl2_1
    | ~ spl2_12 ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_1
    | ~ spl2_12 ),
    inference(superposition,[],[f28,f86])).

fof(f86,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_12
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f28,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f90,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f89,f76,f69,f41,f31,f85])).

fof(f31,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,
    ( spl2_4
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f69,plain,
    ( spl2_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f76,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f89,plain,
    ( ! [X1] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f88,f33])).

fof(f33,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f88,plain,
    ( ! [X1] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1)
    | ~ spl2_4
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f80,f42])).

fof(f42,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f80,plain,
    ( ! [X1] : k2_relat_1(k7_relat_1(k1_xboole_0,X1)) = k9_relat_1(k1_xboole_0,X1)
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(resolution,[],[f77,f71])).

fof(f71,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,
    ( spl2_11
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f74,f53,f45,f76])).

fof(f45,plain,
    ( spl2_5
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f53,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f72,plain,
    ( spl2_10
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f67,f63,f57,f69])).

fof(f57,plain,
    ( spl2_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f63,plain,
    ( spl2_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f67,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(superposition,[],[f59,f65])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f59,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f66,plain,
    ( spl2_9
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f61,f57,f49,f63])).

fof(f49,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f61,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(resolution,[],[f50,f59])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f60,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f15])).

fof(f15,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK1) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f55,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f51,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f47,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f43,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f34,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f31])).

fof(f19,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f29,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f26])).

fof(f17,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (1375)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.41  % (1374)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (1376)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.44  % (1372)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (1372)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f29,f34,f43,f47,f51,f55,f60,f66,f72,f78,f90,f93])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    spl2_1 | ~spl2_12),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    $false | (spl2_1 | ~spl2_12)),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f91])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | (spl2_1 | ~spl2_12)),
% 0.21/0.44    inference(superposition,[],[f28,f86])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl2_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f85])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    spl2_12 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    spl2_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    spl2_12 | ~spl2_2 | ~spl2_4 | ~spl2_10 | ~spl2_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f89,f76,f69,f41,f31,f85])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    spl2_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    spl2_4 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl2_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    spl2_11 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) | ~v1_xboole_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    ( ! [X1] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)) ) | (~spl2_2 | ~spl2_4 | ~spl2_10 | ~spl2_11)),
% 0.21/0.44    inference(forward_demodulation,[],[f88,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f31])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    ( ! [X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1)) ) | (~spl2_4 | ~spl2_10 | ~spl2_11)),
% 0.21/0.44    inference(forward_demodulation,[],[f80,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f41])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X1] : (k2_relat_1(k7_relat_1(k1_xboole_0,X1)) = k9_relat_1(k1_xboole_0,X1)) ) | (~spl2_10 | ~spl2_11)),
% 0.21/0.44    inference(resolution,[],[f77,f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0) | ~spl2_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f69])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_xboole_0(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)) ) | ~spl2_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f76])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    spl2_11 | ~spl2_5 | ~spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f74,f53,f45,f76])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl2_5 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl2_7 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) | ~v1_xboole_0(X0)) ) | (~spl2_5 | ~spl2_7)),
% 0.21/0.44    inference(resolution,[],[f54,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f45])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f53])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl2_10 | ~spl2_8 | ~spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f67,f63,f57,f69])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    spl2_8 <=> v1_xboole_0(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    spl2_9 <=> k1_xboole_0 = sK1),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0) | (~spl2_8 | ~spl2_9)),
% 0.21/0.44    inference(superposition,[],[f59,f65])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    k1_xboole_0 = sK1 | ~spl2_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f63])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    v1_xboole_0(sK1) | ~spl2_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f57])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    spl2_9 | ~spl2_6 | ~spl2_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f61,f57,f49,f63])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl2_6 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    k1_xboole_0 = sK1 | (~spl2_6 | ~spl2_8)),
% 0.21/0.44    inference(resolution,[],[f50,f59])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl2_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f49])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    spl2_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f57])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    v1_xboole_0(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    v1_xboole_0(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK1)),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f53])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl2_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f49])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f45])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f41])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f31])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ~spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f26])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (1372)------------------------------
% 0.21/0.44  % (1372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (1372)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (1372)Memory used [KB]: 10618
% 0.21/0.44  % (1372)Time elapsed: 0.035 s
% 0.21/0.44  % (1372)------------------------------
% 0.21/0.44  % (1372)------------------------------
% 0.21/0.44  % (1365)Success in time 0.088 s
%------------------------------------------------------------------------------
