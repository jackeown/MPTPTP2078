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
% DateTime   : Thu Dec  3 12:49:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  74 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :  123 ( 161 expanded)
%              Number of equality atoms :   34 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f49,f56,f73,f80,f91])).

fof(f91,plain,(
    spl1_10 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl1_10 ),
    inference(subsumption_resolution,[],[f84,f19])).

fof(f19,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f84,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | spl1_10 ),
    inference(resolution,[],[f79,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f79,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl1_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl1_10
  <=> r1_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f80,plain,
    ( ~ spl1_10
    | spl1_1
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f75,f71,f25,f77])).

fof(f25,plain,
    ( spl1_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f71,plain,
    ( spl1_9
  <=> ! [X2] :
        ( ~ r1_xboole_0(k1_xboole_0,X2)
        | k1_xboole_0 = k9_relat_1(k1_xboole_0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f75,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl1_1
    | ~ spl1_9 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl1_1
    | ~ spl1_9 ),
    inference(superposition,[],[f27,f72])).

fof(f72,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)
        | ~ r1_xboole_0(k1_xboole_0,X2) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f27,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f73,plain,
    ( spl1_9
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f69,f54,f46,f40,f71])).

fof(f40,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f46,plain,
    ( spl1_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f54,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f69,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(k1_xboole_0,X2)
        | k1_xboole_0 = k9_relat_1(k1_xboole_0,X2) )
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f64,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f64,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)
        | ~ r1_xboole_0(k1_relat_1(k1_xboole_0),X2) )
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(resolution,[],[f55,f48])).

fof(f48,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k9_relat_1(X0,X1)
        | ~ r1_xboole_0(k1_relat_1(X0),X1) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f56,plain,
    ( spl1_6
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f52,f35,f54])).

fof(f35,plain,
    ( spl1_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),X1) )
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f51,f37])).

fof(f37,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k1_xboole_0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k1_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k1_xboole_0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f49,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f44,f30,f46])).

fof(f30,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f44,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(superposition,[],[f18,f32])).

fof(f32,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f43,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f40])).

fof(f16,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f38,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f15,f30])).

fof(f15,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f28,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f14,f25])).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (20298)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.41  % (20295)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (20297)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (20290)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (20290)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f49,f56,f73,f80,f91])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    spl1_10),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f90])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    $false | spl1_10),
% 0.21/0.43    inference(subsumption_resolution,[],[f84,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,k1_xboole_0) | spl1_10),
% 0.21/0.43    inference(resolution,[],[f79,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_xboole_0,sK0) | spl1_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f77])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    spl1_10 <=> r1_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ~spl1_10 | spl1_1 | ~spl1_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f75,f71,f25,f77])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    spl1_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl1_9 <=> ! [X2] : (~r1_xboole_0(k1_xboole_0,X2) | k1_xboole_0 = k9_relat_1(k1_xboole_0,X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_xboole_0,sK0) | (spl1_1 | ~spl1_9)),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f74])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,sK0) | (spl1_1 | ~spl1_9)),
% 0.21/0.43    inference(superposition,[],[f27,f72])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X2) | ~r1_xboole_0(k1_xboole_0,X2)) ) | ~spl1_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f71])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f25])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl1_9 | ~spl1_4 | ~spl1_5 | ~spl1_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f69,f54,f46,f40,f71])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl1_5 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl1_6 <=> ! [X1,X0] : (k1_xboole_0 = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X2] : (~r1_xboole_0(k1_xboole_0,X2) | k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)) ) | (~spl1_4 | ~spl1_5 | ~spl1_6)),
% 0.21/0.43    inference(forward_demodulation,[],[f64,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f40])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X2) | ~r1_xboole_0(k1_relat_1(k1_xboole_0),X2)) ) | (~spl1_5 | ~spl1_6)),
% 0.21/0.43    inference(resolution,[],[f55,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f46])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,X1) | ~r1_xboole_0(k1_relat_1(X0),X1)) ) | ~spl1_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f54])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl1_6 | ~spl1_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f52,f35,f54])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    spl1_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1)) ) | ~spl1_3),
% 0.21/0.43    inference(forward_demodulation,[],[f51,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f35])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1)) )),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(superposition,[],[f20,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl1_5 | ~spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f44,f30,f46])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0) | ~spl1_2),
% 0.21/0.43    inference(superposition,[],[f18,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f30])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl1_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f40])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl1_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f35])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f15,f30])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ~spl1_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f14,f25])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (20290)------------------------------
% 0.21/0.43  % (20290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (20290)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (20290)Memory used [KB]: 10618
% 0.21/0.43  % (20290)Time elapsed: 0.006 s
% 0.21/0.43  % (20290)------------------------------
% 0.21/0.43  % (20290)------------------------------
% 0.21/0.44  % (20288)Success in time 0.08 s
%------------------------------------------------------------------------------
