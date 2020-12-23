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
% DateTime   : Thu Dec  3 13:16:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 110 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  181 ( 225 expanded)
%              Number of equality atoms :   32 (  51 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f116,f119,f122,f125,f129,f132])).

fof(f132,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f65,f101])).

fof(f101,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_3
  <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f65,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) ),
    inference(backward_demodulation,[],[f37,f41])).

fof(f41,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f37,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f129,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f60,f78])).

fof(f78,plain,
    ( ! [X0] : ~ l1_orders_2(X0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_1
  <=> ! [X0] : ~ l1_orders_2(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f60,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( v3_orders_2(sK1)
    & v1_orders_2(sK1)
    & v7_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( v3_orders_2(X0)
        & v1_orders_2(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0)
        & l1_orders_2(X0) )
   => ( v3_orders_2(sK1)
      & v1_orders_2(sK1)
      & v7_struct_0(sK1)
      & ~ v2_struct_0(sK1)
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] :
      ( v3_orders_2(X0)
      & v1_orders_2(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_0)).

fof(f125,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl2_6 ),
    inference(subsumption_resolution,[],[f38,f123])).

fof(f123,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_6 ),
    inference(resolution,[],[f113,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f113,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f122,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f109,f51])).

fof(f51,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(f109,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl2_5
  <=> v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f119,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f38,f117])).

fof(f117,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_4 ),
    inference(resolution,[],[f105,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f105,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_4
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f116,plain,
    ( ~ spl2_6
    | ~ spl2_5
    | ~ spl2_4
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f115,f99,f80,f103,f107,f111])).

fof(f80,plain,
    ( spl2_2
  <=> v1_yellow_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f115,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f91,f87])).

fof(f87,plain,(
    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f85,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f47,f69])).

fof(f69,plain,(
    ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f40,f49])).

fof(f49,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f40,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f85,plain,(
    ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k7_funcop_1(X0,sK0)) ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f91,plain,
    ( ~ v1_yellow_1(k1_xboole_0)
    | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f68,f71])).

fof(f71,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f67,f39])).

fof(f39,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f67,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f43,f41])).

fof(f43,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_yellow_1(X0)
      | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f48,f41])).

fof(f48,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f83,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f75,f80,f77])).

fof(f75,plain,(
    ! [X0] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f70,f73])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(forward_demodulation,[],[f53,f49])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (20872)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.42  % (20872)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f133,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f83,f116,f119,f122,f125,f129,f132])).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    ~spl2_3),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f130])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    $false | ~spl2_3),
% 0.21/0.42    inference(subsumption_resolution,[],[f65,f101])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f99])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    spl2_3 <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))),
% 0.21/0.42    inference(backward_demodulation,[],[f37,f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,axiom,(
% 0.21/0.42    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f23])).
% 0.21/0.42  fof(f23,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.21/0.42    inference(negated_conjecture,[],[f22])).
% 0.21/0.42  fof(f22,conjecture,(
% 0.21/0.42    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.42  fof(f127,plain,(
% 0.21/0.42    $false | ~spl2_1),
% 0.21/0.42    inference(subsumption_resolution,[],[f60,f78])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    ( ! [X0] : (~l1_orders_2(X0)) ) | ~spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f77])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    spl2_1 <=> ! [X0] : ~l1_orders_2(X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    l1_orders_2(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    v3_orders_2(sK1) & v1_orders_2(sK1) & v7_struct_0(sK1) & ~v2_struct_0(sK1) & l1_orders_2(sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ? [X0] : (v3_orders_2(X0) & v1_orders_2(X0) & v7_struct_0(X0) & ~v2_struct_0(X0) & l1_orders_2(X0)) => (v3_orders_2(sK1) & v1_orders_2(sK1) & v7_struct_0(sK1) & ~v2_struct_0(sK1) & l1_orders_2(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f16,axiom,(
% 0.21/0.42    ? [X0] : (v3_orders_2(X0) & v1_orders_2(X0) & v7_struct_0(X0) & ~v2_struct_0(X0) & l1_orders_2(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_0)).
% 0.21/0.42  fof(f125,plain,(
% 0.21/0.42    spl2_6),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f124])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    $false | spl2_6),
% 0.21/0.42    inference(subsumption_resolution,[],[f38,f123])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    ~v1_xboole_0(k1_xboole_0) | spl2_6),
% 0.21/0.42    inference(resolution,[],[f113,f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    ~v1_relat_1(k1_xboole_0) | spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f111])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    spl2_6 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f122,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.42  fof(f121,plain,(
% 0.21/0.42    $false | spl2_5),
% 0.21/0.42    inference(resolution,[],[f109,f51])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,axiom,(
% 0.21/0.42    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f107])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    spl2_5 <=> v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    $false | spl2_4),
% 0.21/0.42    inference(subsumption_resolution,[],[f38,f117])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    ~v1_xboole_0(k1_xboole_0) | spl2_4),
% 0.21/0.42    inference(resolution,[],[f105,f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    ~v1_funct_1(k1_xboole_0) | spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f103])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl2_4 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    ~spl2_6 | ~spl2_5 | ~spl2_4 | ~spl2_2 | spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f115,f99,f80,f103,f107,f111])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl2_2 <=> v1_yellow_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(forward_demodulation,[],[f91,f87])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.42    inference(superposition,[],[f85,f73])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)) )),
% 0.21/0.42    inference(resolution,[],[f47,f69])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))) )),
% 0.21/0.42    inference(backward_demodulation,[],[f40,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f20,axiom,(
% 0.21/0.42    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,axiom,(
% 0.21/0.42    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k7_funcop_1(X0,sK0))) )),
% 0.21/0.42    inference(resolution,[],[f54,f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    l1_orders_2(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f33])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,axiom,(
% 0.21/0.42    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    ~v1_yellow_1(k1_xboole_0) | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(resolution,[],[f68,f71])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.42    inference(superposition,[],[f67,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,axiom,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0] : (v1_partfun1(k6_relat_1(X0),X0)) )),
% 0.21/0.42    inference(forward_demodulation,[],[f43,f41])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,axiom,(
% 0.21/0.42    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_partfun1(X0,k1_xboole_0) | ~v1_yellow_1(X0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(forward_demodulation,[],[f48,f41])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f21])).
% 0.21/0.42  fof(f21,axiom,(
% 0.21/0.42    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl2_1 | spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f75,f80,f77])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X0] : (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.21/0.42    inference(superposition,[],[f70,f73])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_yellow_1(k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.42    inference(forward_demodulation,[],[f53,f49])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f18])).
% 0.21/0.42  fof(f18,axiom,(
% 0.21/0.42    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (20872)------------------------------
% 0.21/0.42  % (20872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (20872)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (20872)Memory used [KB]: 6140
% 0.21/0.42  % (20872)Time elapsed: 0.006 s
% 0.21/0.42  % (20872)------------------------------
% 0.21/0.42  % (20872)------------------------------
% 0.21/0.42  % (20855)Success in time 0.064 s
%------------------------------------------------------------------------------
