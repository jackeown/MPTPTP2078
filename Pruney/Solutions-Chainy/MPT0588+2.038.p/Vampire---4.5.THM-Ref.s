%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 116 expanded)
%              Number of leaves         :   20 (  55 expanded)
%              Depth                    :    6
%              Number of atoms          :  183 ( 290 expanded)
%              Number of equality atoms :   36 (  56 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f738,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f51,f56,f68,f72,f91,f110,f137,f142,f222,f577,f734,f737])).

fof(f737,plain,
    ( spl2_2
    | ~ spl2_38
    | ~ spl2_41 ),
    inference(avatar_contradiction_clause,[],[f736])).

fof(f736,plain,
    ( $false
    | spl2_2
    | ~ spl2_38
    | ~ spl2_41 ),
    inference(subsumption_resolution,[],[f46,f735])).

fof(f735,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_38
    | ~ spl2_41 ),
    inference(forward_demodulation,[],[f733,f576])).

fof(f576,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f575])).

fof(f575,plain,
    ( spl2_38
  <=> ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f733,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f732])).

fof(f732,plain,
    ( spl2_41
  <=> ! [X0] : k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f46,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_2
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f734,plain,
    ( spl2_41
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f143,f140,f108,f39,f732])).

fof(f39,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f108,plain,
    ( spl2_13
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f140,plain,
    ( spl2_18
  <=> ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f143,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_1
    | ~ spl2_13
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f41,f141,f109])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f141,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f41,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f577,plain,
    ( spl2_38
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f223,f220,f70,f39,f575])).

fof(f70,plain,
    ( spl2_8
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f220,plain,
    ( spl2_25
  <=> ! [X3,X2] :
        ( k7_relat_1(X2,X3) = k7_relat_1(k7_relat_1(X2,X3),k3_xboole_0(k1_relat_1(X2),X3))
        | ~ v1_relat_1(k7_relat_1(X2,X3))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f223,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f41,f71,f221])).

fof(f221,plain,
    ( ! [X2,X3] :
        ( k7_relat_1(X2,X3) = k7_relat_1(k7_relat_1(X2,X3),k3_xboole_0(k1_relat_1(X2),X3))
        | ~ v1_relat_1(k7_relat_1(X2,X3))
        | ~ v1_relat_1(X2) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f220])).

fof(f71,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f222,plain,
    ( spl2_25
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f104,f89,f54,f220])).

fof(f54,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f89,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f104,plain,
    ( ! [X2,X3] :
        ( k7_relat_1(X2,X3) = k7_relat_1(k7_relat_1(X2,X3),k3_xboole_0(k1_relat_1(X2),X3))
        | ~ v1_relat_1(k7_relat_1(X2,X3))
        | ~ v1_relat_1(X2) )
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(superposition,[],[f55,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f55,plain,
    ( ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f142,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f138,f135,f89,f39,f140])).

fof(f135,plain,
    ( spl2_17
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f138,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f136,f100])).

fof(f100,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f41,f90])).

fof(f136,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,
    ( spl2_17
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f80,f66,f39,f135])).

fof(f66,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f80,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f41,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f110,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f34,f108])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f91,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f32,f89])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f72,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f52,f49,f39,f70])).

fof(f49,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f52,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f41,f50])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f68,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f56,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f51,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f30,f49])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f47,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f25,f44])).

fof(f25,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f42,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (16583)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (16580)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (16583)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f738,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f42,f47,f51,f56,f68,f72,f91,f110,f137,f142,f222,f577,f734,f737])).
% 0.21/0.49  fof(f737,plain,(
% 0.21/0.49    spl2_2 | ~spl2_38 | ~spl2_41),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f736])).
% 0.21/0.49  fof(f736,plain,(
% 0.21/0.49    $false | (spl2_2 | ~spl2_38 | ~spl2_41)),
% 0.21/0.49    inference(subsumption_resolution,[],[f46,f735])).
% 0.21/0.49  fof(f735,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))) ) | (~spl2_38 | ~spl2_41)),
% 0.21/0.49    inference(forward_demodulation,[],[f733,f576])).
% 0.21/0.49  fof(f576,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0))) ) | ~spl2_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f575])).
% 0.21/0.49  fof(f575,plain,(
% 0.21/0.49    spl2_38 <=> ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.21/0.49  fof(f733,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))) ) | ~spl2_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f732])).
% 0.21/0.49  fof(f732,plain,(
% 0.21/0.49    spl2_41 <=> ! [X0] : k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) | spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    spl2_2 <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f734,plain,(
% 0.21/0.49    spl2_41 | ~spl2_1 | ~spl2_13 | ~spl2_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f143,f140,f108,f39,f732])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl2_13 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl2_18 <=> ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))) ) | (~spl2_1 | ~spl2_13 | ~spl2_18)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f41,f141,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) ) | ~spl2_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)) ) | ~spl2_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f39])).
% 0.21/0.49  fof(f577,plain,(
% 0.21/0.49    spl2_38 | ~spl2_1 | ~spl2_8 | ~spl2_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f223,f220,f70,f39,f575])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl2_8 <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    spl2_25 <=> ! [X3,X2] : (k7_relat_1(X2,X3) = k7_relat_1(k7_relat_1(X2,X3),k3_xboole_0(k1_relat_1(X2),X3)) | ~v1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0))) ) | (~spl2_1 | ~spl2_8 | ~spl2_25)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f41,f71,f221])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k7_relat_1(X2,X3) = k7_relat_1(k7_relat_1(X2,X3),k3_xboole_0(k1_relat_1(X2),X3)) | ~v1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2)) ) | ~spl2_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f220])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    spl2_25 | ~spl2_4 | ~spl2_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f104,f89,f54,f220])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl2_4 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl2_11 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k7_relat_1(X2,X3) = k7_relat_1(k7_relat_1(X2,X3),k3_xboole_0(k1_relat_1(X2),X3)) | ~v1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2)) ) | (~spl2_4 | ~spl2_11)),
% 0.21/0.49    inference(superposition,[],[f55,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) ) | ~spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl2_18 | ~spl2_1 | ~spl2_11 | ~spl2_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f138,f135,f89,f39,f140])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl2_17 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)) ) | (~spl2_1 | ~spl2_11 | ~spl2_17)),
% 0.21/0.49    inference(forward_demodulation,[],[f136,f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | (~spl2_1 | ~spl2_11)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f41,f90])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) ) | ~spl2_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f135])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl2_17 | ~spl2_1 | ~spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f80,f66,f39,f135])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl2_7 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_7)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f41,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl2_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl2_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f108])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl2_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f89])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl2_8 | ~spl2_1 | ~spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f49,f39,f70])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl2_3 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | (~spl2_1 | ~spl2_3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f41,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f66])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f54])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f49])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f44])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f39])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (16583)------------------------------
% 0.21/0.49  % (16583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (16583)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (16583)Memory used [KB]: 6652
% 0.21/0.49  % (16583)Time elapsed: 0.058 s
% 0.21/0.49  % (16583)------------------------------
% 0.21/0.49  % (16583)------------------------------
% 0.21/0.49  % (16584)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (16577)Success in time 0.13 s
%------------------------------------------------------------------------------
