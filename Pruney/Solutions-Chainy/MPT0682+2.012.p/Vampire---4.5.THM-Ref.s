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
% DateTime   : Thu Dec  3 12:53:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 220 expanded)
%              Number of equality atoms :   42 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f47,f51,f63,f75,f79,f91,f111,f125])).

fof(f125,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f46,f123])).

fof(f123,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k9_relat_1(sK2,X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f122,f84])).

fof(f84,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f36,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f36,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f122,plain,
    ( ! [X0,X1] : k9_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1) = k3_xboole_0(X0,k9_relat_1(sK2,X1))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f114,f101])).

fof(f101,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f100,f62])).

fof(f62,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f100,plain,
    ( ! [X0,X1] : k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f99,f74])).

fof(f74,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_10
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f99,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f95,f62])).

fof(f95,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f50,f50,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f50,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f114,plain,
    ( ! [X0,X1] : k9_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1) = k9_relat_1(k6_relat_1(X0),k9_relat_1(sK2,X1))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f36,f50,f110])).

fof(f110,plain,
    ( ! [X2,X0,X1] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f46,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_3
  <=> k9_relat_1(k8_relat_1(sK0,sK2),sK1) = k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f111,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f31,f109])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f91,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f26,f89])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f79,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f30,f77])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f75,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f47,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:51:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (13106)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (13102)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (13103)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (13106)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f37,f47,f51,f63,f75,f79,f91,f111,f125])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ~spl3_1 | spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_13 | ~spl3_14),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f124])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    $false | (~spl3_1 | spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_13 | ~spl3_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f46,f123])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(sK2,X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1)) ) | (~spl3_1 | ~spl3_4 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_13 | ~spl3_14)),
% 0.21/0.47    inference(forward_demodulation,[],[f122,f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) ) | (~spl3_1 | ~spl3_11)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f36,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | ~spl3_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl3_11 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k9_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1) = k3_xboole_0(X0,k9_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_4 | ~spl3_7 | ~spl3_10 | ~spl3_13 | ~spl3_14)),
% 0.21/0.47    inference(forward_demodulation,[],[f114,f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl3_4 | ~spl3_7 | ~spl3_10 | ~spl3_13)),
% 0.21/0.47    inference(forward_demodulation,[],[f100,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl3_7 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl3_4 | ~spl3_7 | ~spl3_10 | ~spl3_13)),
% 0.21/0.47    inference(forward_demodulation,[],[f99,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl3_10 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl3_4 | ~spl3_7 | ~spl3_13)),
% 0.21/0.47    inference(forward_demodulation,[],[f95,f62])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))) ) | (~spl3_4 | ~spl3_13)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f50,f50,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl3_13 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl3_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k9_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1) = k9_relat_1(k6_relat_1(X0),k9_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_4 | ~spl3_14)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f36,f50,f110])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl3_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    spl3_14 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) | spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl3_3 <=> k9_relat_1(k8_relat_1(sK0,sK2),sK1) = k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl3_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f109])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl3_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f89])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl3_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f77])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f73])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f61])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f49])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f44])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f34])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (13106)------------------------------
% 0.21/0.47  % (13106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13106)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (13106)Memory used [KB]: 6140
% 0.21/0.47  % (13106)Time elapsed: 0.063 s
% 0.21/0.47  % (13106)------------------------------
% 0.21/0.47  % (13106)------------------------------
% 0.21/0.48  % (13098)Success in time 0.114 s
%------------------------------------------------------------------------------
