%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 108 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  177 ( 261 expanded)
%              Number of equality atoms :   52 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f48,f56,f64,f76,f80,f96,f116,f120,f171,f187,f227])).

fof(f227,plain,
    ( ~ spl3_7
    | spl3_24 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl3_7
    | spl3_24 ),
    inference(unit_resulting_resolution,[],[f63,f186])).

fof(f186,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0)
    | spl3_24 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl3_24
  <=> k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) = k3_xboole_0(k10_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f63,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f187,plain,
    ( ~ spl3_24
    | spl3_2
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f172,f169,f41,f184])).

fof(f41,plain,
    ( spl3_2
  <=> k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f169,plain,
    ( spl3_22
  <=> ! [X1,X0] : k3_xboole_0(k10_relat_1(sK2,X1),X0) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f172,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0)
    | spl3_2
    | ~ spl3_22 ),
    inference(superposition,[],[f43,f170])).

fof(f170,plain,
    ( ! [X0,X1] : k3_xboole_0(k10_relat_1(sK2,X1),X0) = k10_relat_1(k7_relat_1(sK2,X0),X1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f169])).

fof(f43,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f171,plain,
    ( spl3_22
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f134,f118,f114,f94,f74,f54,f46,f36,f169])).

fof(f36,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f46,plain,
    ( spl3_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( spl3_5
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f74,plain,
    ( spl3_10
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f94,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

% (6503)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% (6517)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% (6514)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% (6504)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f114,plain,
    ( spl3_15
  <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f118,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f134,plain,
    ( ! [X0,X1] : k3_xboole_0(k10_relat_1(sK2,X1),X0) = k10_relat_1(k7_relat_1(sK2,X0),X1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f133,f115])).

fof(f115,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f133,plain,
    ( ! [X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k3_xboole_0(k10_relat_1(sK2,X1),X0)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f122,f106])).

fof(f106,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f105,f55])).

fof(f55,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f105,plain,
    ( ! [X0,X1] : k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f104,f75])).

fof(f75,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f104,plain,
    ( ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f100,f55])).

fof(f100,plain,
    ( ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f47,f47,f95])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f47,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f122,plain,
    ( ! [X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f47,f38,f119])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f38,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f120,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f32,f118])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f116,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f85,f78,f36,f114])).

fof(f78,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f85,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f38,f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f96,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f26,f94])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f80,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f76,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f64,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f56,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f48,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f44,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f39,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:47:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (6507)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.44  % (6507)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f228,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f39,f44,f48,f56,f64,f76,f80,f96,f116,f120,f171,f187,f227])).
% 0.20/0.44  fof(f227,plain,(
% 0.20/0.44    ~spl3_7 | spl3_24),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f220])).
% 0.20/0.44  fof(f220,plain,(
% 0.20/0.44    $false | (~spl3_7 | spl3_24)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f63,f186])).
% 0.20/0.44  fof(f186,plain,(
% 0.20/0.44    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0) | spl3_24),
% 0.20/0.44    inference(avatar_component_clause,[],[f184])).
% 0.20/0.44  fof(f184,plain,(
% 0.20/0.44    spl3_24 <=> k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) = k3_xboole_0(k10_relat_1(sK2,sK1),sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f62])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    spl3_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.44  fof(f187,plain,(
% 0.20/0.44    ~spl3_24 | spl3_2 | ~spl3_22),
% 0.20/0.44    inference(avatar_split_clause,[],[f172,f169,f41,f184])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    spl3_2 <=> k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.44  fof(f169,plain,(
% 0.20/0.44    spl3_22 <=> ! [X1,X0] : k3_xboole_0(k10_relat_1(sK2,X1),X0) = k10_relat_1(k7_relat_1(sK2,X0),X1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.44  fof(f172,plain,(
% 0.20/0.44    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0) | (spl3_2 | ~spl3_22)),
% 0.20/0.44    inference(superposition,[],[f43,f170])).
% 0.20/0.44  fof(f170,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(k10_relat_1(sK2,X1),X0) = k10_relat_1(k7_relat_1(sK2,X0),X1)) ) | ~spl3_22),
% 0.20/0.44    inference(avatar_component_clause,[],[f169])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) | spl3_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f41])).
% 0.20/0.44  fof(f171,plain,(
% 0.20/0.44    spl3_22 | ~spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_14 | ~spl3_15 | ~spl3_16),
% 0.20/0.44    inference(avatar_split_clause,[],[f134,f118,f114,f94,f74,f54,f46,f36,f169])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    spl3_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    spl3_5 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    spl3_10 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    spl3_14 <=> ! [X1,X0] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.45  % (6503)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.45  % (6517)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (6514)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (6504)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    spl3_15 <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    spl3_16 <=> ! [X1,X0,X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.46  fof(f134,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(k10_relat_1(sK2,X1),X0) = k10_relat_1(k7_relat_1(sK2,X0),X1)) ) | (~spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_14 | ~spl3_15 | ~spl3_16)),
% 0.20/0.46    inference(forward_demodulation,[],[f133,f115])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | ~spl3_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f114])).
% 0.20/0.46  fof(f133,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k3_xboole_0(k10_relat_1(sK2,X1),X0)) ) | (~spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_14 | ~spl3_16)),
% 0.20/0.46    inference(forward_demodulation,[],[f122,f106])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_14)),
% 0.20/0.46    inference(forward_demodulation,[],[f105,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f54])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_14)),
% 0.20/0.46    inference(forward_demodulation,[],[f104,f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl3_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f74])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl3_3 | ~spl3_5 | ~spl3_14)),
% 0.20/0.46    inference(forward_demodulation,[],[f100,f55])).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))) ) | (~spl3_3 | ~spl3_14)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f47,f47,f95])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f94])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f46])).
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_3 | ~spl3_16)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f47,f38,f119])).
% 0.20/0.46  fof(f119,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl3_16),
% 0.20/0.46    inference(avatar_component_clause,[],[f118])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f36])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    spl3_16),
% 0.20/0.46    inference(avatar_split_clause,[],[f32,f118])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    spl3_15 | ~spl3_1 | ~spl3_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f85,f78,f36,f114])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    spl3_11 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | (~spl3_1 | ~spl3_11)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f38,f79])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) ) | ~spl3_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f78])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    spl3_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f94])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    spl3_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f31,f78])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    spl3_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f30,f74])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    spl3_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f62])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f54])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f46])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ~spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f41])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2)) => (k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.20/0.46    inference(negated_conjecture,[],[f12])).
% 0.20/0.46  fof(f12,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f36])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    v1_relat_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (6507)------------------------------
% 0.20/0.46  % (6507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (6507)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (6507)Memory used [KB]: 6268
% 0.20/0.46  % (6507)Time elapsed: 0.047 s
% 0.20/0.46  % (6507)------------------------------
% 0.20/0.46  % (6507)------------------------------
% 0.20/0.47  % (6497)Success in time 0.112 s
%------------------------------------------------------------------------------
