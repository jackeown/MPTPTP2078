%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  65 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :  106 ( 160 expanded)
%              Number of equality atoms :   26 (  55 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7916)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f42,f52,f58,f60,f62])).

fof(f62,plain,
    ( spl1_5
    | ~ spl1_1
    | ~ spl1_6
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f61,f35,f49,f25,f45])).

fof(f45,plain,
    ( spl1_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f25,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f49,plain,
    ( spl1_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f35,plain,
    ( spl1_3
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f61,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl1_3 ),
    inference(superposition,[],[f22,f37])).

fof(f37,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f60,plain,
    ( spl1_2
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl1_2
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f32,f47,f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f47,plain,
    ( v1_xboole_0(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f32,plain,
    ( k1_xboole_0 != sK0
    | spl1_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl1_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f58,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | spl1_6 ),
    inference(unit_resulting_resolution,[],[f23,f51])).

fof(f51,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f18,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f52,plain,
    ( spl1_5
    | ~ spl1_1
    | ~ spl1_6
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f43,f39,f49,f25,f45])).

fof(f39,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f43,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl1_4 ),
    inference(superposition,[],[f21,f41])).

fof(f41,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f42,plain,
    ( spl1_3
    | spl1_4 ),
    inference(avatar_split_clause,[],[f15,f39,f35])).

fof(f15,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ( k1_xboole_0 = k2_relat_1(X0)
            | k1_xboole_0 = k1_relat_1(X0) )
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f33,plain,(
    ~ spl1_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f16,f25])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (7924)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (7912)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (7934)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (7917)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (7937)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (7926)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (7934)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (7918)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  % (7916)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f28,f33,f42,f52,f58,f60,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    spl1_5 | ~spl1_1 | ~spl1_6 | ~spl1_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f61,f35,f49,f25,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    spl1_5 <=> v1_xboole_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    spl1_1 <=> v1_relat_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    spl1_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    spl1_3 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | v1_xboole_0(sK0) | ~spl1_3),
% 0.21/0.53    inference(superposition,[],[f22,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f35])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl1_2 | ~spl1_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    $false | (spl1_2 | ~spl1_5)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f32,f47,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    v1_xboole_0(sK0) | ~spl1_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f45])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    k1_xboole_0 != sK0 | spl1_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    spl1_2 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    spl1_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    $false | spl1_6),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f23,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | spl1_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f49])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(definition_unfolding,[],[f18,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    spl1_5 | ~spl1_1 | ~spl1_6 | ~spl1_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f39,f49,f25,f45])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    spl1_4 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | v1_xboole_0(sK0) | ~spl1_4),
% 0.21/0.53    inference(superposition,[],[f21,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(sK0) | ~spl1_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f39])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    spl1_3 | spl1_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f15,f39,f35])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(sK0) | k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ? [X0] : ((k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f6])).
% 0.21/0.53  fof(f6,conjecture,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ~spl1_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f17,f30])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    spl1_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f16,f25])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    v1_relat_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (7934)------------------------------
% 0.21/0.53  % (7934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7934)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (7934)Memory used [KB]: 10618
% 0.21/0.53  % (7934)Time elapsed: 0.082 s
% 0.21/0.53  % (7934)------------------------------
% 0.21/0.53  % (7934)------------------------------
% 0.21/0.53  % (7929)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (7911)Success in time 0.169 s
%------------------------------------------------------------------------------
