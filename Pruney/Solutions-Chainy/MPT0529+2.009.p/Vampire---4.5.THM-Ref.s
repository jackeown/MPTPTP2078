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
% DateTime   : Thu Dec  3 12:48:59 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 111 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :  192 ( 307 expanded)
%              Number of equality atoms :   39 (  67 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f55,f59,f66,f74,f83,f107,f122,f127])).

fof(f127,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f123,f28])).

fof(f28,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_1
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f123,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(resolution,[],[f121,f33])).

fof(f33,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f122,plain,
    ( spl3_19
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f118,f105,f45,f36,f120])).

fof(f36,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f45,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f105,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ v1_relat_1(k8_relat_1(X0,sK2))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f117,f38])).

fof(f38,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(resolution,[],[f106,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k8_relat_1(X0,sK2))
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl3_16
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f100,f81,f63,f105])).

fof(f63,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_xboole_0(X1,X0),X2)
        | ~ r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f81,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK2),X0),X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ v1_relat_1(k8_relat_1(X0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ v1_relat_1(k8_relat_1(X0,sK2))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(resolution,[],[f82,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_xboole_0(X1,X0),X2)
        | ~ r1_tarski(X0,X2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK2),X0),X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ v1_relat_1(k8_relat_1(X0,sK2)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,
    ( spl3_12
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f79,f72,f53,f81])).

fof(f53,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f72,plain,
    ( spl3_10
  <=> ! [X0] : k2_relat_1(k8_relat_1(X0,sK2)) = k3_xboole_0(k2_relat_1(sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK2),X0),X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))
        | ~ v1_relat_1(k8_relat_1(X0,sK2)) )
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(superposition,[],[f54,f73])).

fof(f73,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK2)) = k3_xboole_0(k2_relat_1(sK2),X0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f74,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f69,f49,f36,f72])).

fof(f49,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f69,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK2)) = k3_xboole_0(k2_relat_1(sK2),X0)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f50,f38])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f66,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f61,f57,f41,f63])).

fof(f41,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f61,plain,
    ( ! [X4,X5,X3] :
        ( r1_tarski(k3_xboole_0(X4,X3),X5)
        | ~ r1_tarski(X3,X5) )
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f58,f42])).

fof(f42,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f55,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f51,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f47,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(f34,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f26])).

fof(f19,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:02:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.42  % (4594)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.15/0.42  % (4595)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.15/0.43  % (4595)Refutation found. Thanks to Tanya!
% 0.15/0.43  % SZS status Theorem for theBenchmark
% 0.15/0.43  % SZS output start Proof for theBenchmark
% 0.15/0.43  fof(f136,plain,(
% 0.15/0.43    $false),
% 0.15/0.43    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f55,f59,f66,f74,f83,f107,f122,f127])).
% 0.15/0.43  fof(f127,plain,(
% 0.15/0.43    spl3_1 | ~spl3_2 | ~spl3_19),
% 0.15/0.43    inference(avatar_contradiction_clause,[],[f126])).
% 0.15/0.43  fof(f126,plain,(
% 0.15/0.43    $false | (spl3_1 | ~spl3_2 | ~spl3_19)),
% 0.15/0.43    inference(subsumption_resolution,[],[f123,f28])).
% 0.15/0.43  fof(f28,plain,(
% 0.15/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | spl3_1),
% 0.15/0.43    inference(avatar_component_clause,[],[f26])).
% 0.15/0.43  fof(f26,plain,(
% 0.15/0.43    spl3_1 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.15/0.43  fof(f123,plain,(
% 0.15/0.43    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | (~spl3_2 | ~spl3_19)),
% 0.15/0.43    inference(resolution,[],[f121,f33])).
% 0.15/0.43  fof(f33,plain,(
% 0.15/0.43    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.15/0.43    inference(avatar_component_clause,[],[f31])).
% 0.15/0.43  fof(f31,plain,(
% 0.15/0.43    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.15/0.43  fof(f121,plain,(
% 0.15/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2))) ) | ~spl3_19),
% 0.15/0.43    inference(avatar_component_clause,[],[f120])).
% 0.15/0.43  fof(f120,plain,(
% 0.15/0.43    spl3_19 <=> ! [X1,X0] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(X0,X1))),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.15/0.43  fof(f122,plain,(
% 0.15/0.43    spl3_19 | ~spl3_3 | ~spl3_5 | ~spl3_16),
% 0.15/0.43    inference(avatar_split_clause,[],[f118,f105,f45,f36,f120])).
% 0.15/0.43  fof(f36,plain,(
% 0.15/0.43    spl3_3 <=> v1_relat_1(sK2)),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.15/0.43  fof(f45,plain,(
% 0.15/0.43    spl3_5 <=> ! [X1,X0] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.15/0.43  fof(f105,plain,(
% 0.15/0.43    spl3_16 <=> ! [X1,X0] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~v1_relat_1(k8_relat_1(X0,sK2)) | ~r1_tarski(X0,X1))),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.15/0.43  fof(f118,plain,(
% 0.15/0.43    ( ! [X0,X1] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(X0,X1)) ) | (~spl3_3 | ~spl3_5 | ~spl3_16)),
% 0.15/0.43    inference(subsumption_resolution,[],[f117,f38])).
% 0.15/0.43  fof(f38,plain,(
% 0.15/0.43    v1_relat_1(sK2) | ~spl3_3),
% 0.15/0.43    inference(avatar_component_clause,[],[f36])).
% 0.15/0.43  fof(f117,plain,(
% 0.15/0.43    ( ! [X0,X1] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(sK2)) ) | (~spl3_5 | ~spl3_16)),
% 0.15/0.43    inference(resolution,[],[f106,f46])).
% 0.15/0.43  fof(f46,plain,(
% 0.15/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.15/0.43    inference(avatar_component_clause,[],[f45])).
% 0.15/0.43  fof(f106,plain,(
% 0.15/0.43    ( ! [X0,X1] : (~v1_relat_1(k8_relat_1(X0,sK2)) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~r1_tarski(X0,X1)) ) | ~spl3_16),
% 0.15/0.43    inference(avatar_component_clause,[],[f105])).
% 0.15/0.43  fof(f107,plain,(
% 0.15/0.43    spl3_16 | ~spl3_9 | ~spl3_12),
% 0.15/0.43    inference(avatar_split_clause,[],[f100,f81,f63,f105])).
% 0.15/0.43  fof(f63,plain,(
% 0.15/0.43    spl3_9 <=> ! [X1,X0,X2] : (r1_tarski(k3_xboole_0(X1,X0),X2) | ~r1_tarski(X0,X2))),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.15/0.43  fof(f81,plain,(
% 0.15/0.43    spl3_12 <=> ! [X1,X0] : (~r1_tarski(k3_xboole_0(k2_relat_1(sK2),X0),X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~v1_relat_1(k8_relat_1(X0,sK2)))),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.15/0.43  fof(f100,plain,(
% 0.15/0.43    ( ! [X0,X1] : (k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~v1_relat_1(k8_relat_1(X0,sK2)) | ~r1_tarski(X0,X1)) ) | (~spl3_9 | ~spl3_12)),
% 0.15/0.43    inference(resolution,[],[f82,f64])).
% 0.15/0.43  fof(f64,plain,(
% 0.15/0.43    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X2) | ~r1_tarski(X0,X2)) ) | ~spl3_9),
% 0.15/0.43    inference(avatar_component_clause,[],[f63])).
% 0.15/0.43  fof(f82,plain,(
% 0.15/0.43    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(k2_relat_1(sK2),X0),X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~v1_relat_1(k8_relat_1(X0,sK2))) ) | ~spl3_12),
% 0.15/0.43    inference(avatar_component_clause,[],[f81])).
% 0.15/0.43  fof(f83,plain,(
% 0.15/0.43    spl3_12 | ~spl3_7 | ~spl3_10),
% 0.15/0.43    inference(avatar_split_clause,[],[f79,f72,f53,f81])).
% 0.15/0.43  fof(f53,plain,(
% 0.15/0.43    spl3_7 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.15/0.43  fof(f72,plain,(
% 0.15/0.43    spl3_10 <=> ! [X0] : k2_relat_1(k8_relat_1(X0,sK2)) = k3_xboole_0(k2_relat_1(sK2),X0)),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.15/0.43  fof(f79,plain,(
% 0.15/0.43    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(k2_relat_1(sK2),X0),X1) | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) | ~v1_relat_1(k8_relat_1(X0,sK2))) ) | (~spl3_7 | ~spl3_10)),
% 0.15/0.43    inference(superposition,[],[f54,f73])).
% 0.15/0.43  fof(f73,plain,(
% 0.15/0.43    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK2)) = k3_xboole_0(k2_relat_1(sK2),X0)) ) | ~spl3_10),
% 0.15/0.43    inference(avatar_component_clause,[],[f72])).
% 0.15/0.43  fof(f54,plain,(
% 0.15/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) ) | ~spl3_7),
% 0.15/0.43    inference(avatar_component_clause,[],[f53])).
% 0.15/0.43  fof(f74,plain,(
% 0.15/0.43    spl3_10 | ~spl3_3 | ~spl3_6),
% 0.15/0.43    inference(avatar_split_clause,[],[f69,f49,f36,f72])).
% 0.15/0.43  fof(f49,plain,(
% 0.15/0.43    spl3_6 <=> ! [X1,X0] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.15/0.43  fof(f69,plain,(
% 0.15/0.43    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK2)) = k3_xboole_0(k2_relat_1(sK2),X0)) ) | (~spl3_3 | ~spl3_6)),
% 0.15/0.43    inference(resolution,[],[f50,f38])).
% 0.15/0.43  fof(f50,plain,(
% 0.15/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)) ) | ~spl3_6),
% 0.15/0.43    inference(avatar_component_clause,[],[f49])).
% 0.15/0.43  fof(f66,plain,(
% 0.15/0.43    spl3_9 | ~spl3_4 | ~spl3_8),
% 0.15/0.43    inference(avatar_split_clause,[],[f61,f57,f41,f63])).
% 0.15/0.43  fof(f41,plain,(
% 0.15/0.43    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.15/0.43  fof(f57,plain,(
% 0.15/0.43    spl3_8 <=> ! [X1,X0,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.15/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.15/0.43  fof(f61,plain,(
% 0.15/0.43    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(X4,X3),X5) | ~r1_tarski(X3,X5)) ) | (~spl3_4 | ~spl3_8)),
% 0.15/0.43    inference(superposition,[],[f58,f42])).
% 0.15/0.43  fof(f42,plain,(
% 0.15/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.15/0.43    inference(avatar_component_clause,[],[f41])).
% 0.15/0.43  fof(f58,plain,(
% 0.15/0.43    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.15/0.43    inference(avatar_component_clause,[],[f57])).
% 0.15/0.43  fof(f59,plain,(
% 0.15/0.43    spl3_8),
% 0.15/0.43    inference(avatar_split_clause,[],[f24,f57])).
% 0.15/0.43  fof(f24,plain,(
% 0.15/0.43    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.15/0.43    inference(cnf_transformation,[],[f14])).
% 0.15/0.43  fof(f14,plain,(
% 0.15/0.43    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.15/0.43    inference(ennf_transformation,[],[f2])).
% 0.15/0.43  fof(f2,axiom,(
% 0.15/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.15/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.15/0.43  fof(f55,plain,(
% 0.15/0.43    spl3_7),
% 0.15/0.43    inference(avatar_split_clause,[],[f23,f53])).
% 0.15/0.43  fof(f23,plain,(
% 0.15/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.15/0.43    inference(cnf_transformation,[],[f13])).
% 0.15/0.43  fof(f13,plain,(
% 0.15/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.15/0.43    inference(flattening,[],[f12])).
% 0.15/0.43  fof(f12,plain,(
% 0.15/0.43    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.15/0.43    inference(ennf_transformation,[],[f5])).
% 0.15/0.43  fof(f5,axiom,(
% 0.15/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.15/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.15/0.43  fof(f51,plain,(
% 0.15/0.43    spl3_6),
% 0.15/0.43    inference(avatar_split_clause,[],[f22,f49])).
% 0.15/0.43  fof(f22,plain,(
% 0.15/0.43    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.15/0.43    inference(cnf_transformation,[],[f11])).
% 0.15/0.43  fof(f11,plain,(
% 0.15/0.43    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.15/0.43    inference(ennf_transformation,[],[f4])).
% 0.15/0.43  fof(f4,axiom,(
% 0.15/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.15/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.15/0.43  fof(f47,plain,(
% 0.15/0.43    spl3_5),
% 0.15/0.43    inference(avatar_split_clause,[],[f21,f45])).
% 0.15/0.43  fof(f21,plain,(
% 0.15/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.15/0.43    inference(cnf_transformation,[],[f10])).
% 0.15/0.43  fof(f10,plain,(
% 0.15/0.43    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.15/0.43    inference(ennf_transformation,[],[f3])).
% 0.15/0.43  fof(f3,axiom,(
% 0.15/0.43    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.15/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.15/0.43  fof(f43,plain,(
% 0.15/0.43    spl3_4),
% 0.15/0.43    inference(avatar_split_clause,[],[f20,f41])).
% 0.15/0.43  fof(f20,plain,(
% 0.15/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.15/0.43    inference(cnf_transformation,[],[f1])).
% 0.15/0.43  fof(f1,axiom,(
% 0.15/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.15/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.15/0.43  fof(f39,plain,(
% 0.15/0.43    spl3_3),
% 0.15/0.43    inference(avatar_split_clause,[],[f17,f36])).
% 0.15/0.43  fof(f17,plain,(
% 0.15/0.43    v1_relat_1(sK2)),
% 0.15/0.43    inference(cnf_transformation,[],[f16])).
% 0.15/0.43  fof(f16,plain,(
% 0.15/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.15/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).
% 0.15/0.43  fof(f15,plain,(
% 0.15/0.43    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.15/0.43    introduced(choice_axiom,[])).
% 0.15/0.43  fof(f9,plain,(
% 0.15/0.43    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.15/0.43    inference(flattening,[],[f8])).
% 0.15/0.43  fof(f8,plain,(
% 0.15/0.43    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.15/0.43    inference(ennf_transformation,[],[f7])).
% 0.15/0.43  fof(f7,negated_conjecture,(
% 0.15/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.15/0.43    inference(negated_conjecture,[],[f6])).
% 0.15/0.43  fof(f6,conjecture,(
% 0.15/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.15/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).
% 0.15/0.43  fof(f34,plain,(
% 0.15/0.43    spl3_2),
% 0.15/0.43    inference(avatar_split_clause,[],[f18,f31])).
% 0.15/0.43  fof(f18,plain,(
% 0.15/0.43    r1_tarski(sK0,sK1)),
% 0.15/0.43    inference(cnf_transformation,[],[f16])).
% 0.15/0.43  fof(f29,plain,(
% 0.15/0.43    ~spl3_1),
% 0.15/0.43    inference(avatar_split_clause,[],[f19,f26])).
% 0.15/0.43  fof(f19,plain,(
% 0.15/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.15/0.43    inference(cnf_transformation,[],[f16])).
% 0.15/0.43  % SZS output end Proof for theBenchmark
% 0.15/0.43  % (4595)------------------------------
% 0.15/0.43  % (4595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.43  % (4595)Termination reason: Refutation
% 0.15/0.43  
% 0.15/0.43  % (4595)Memory used [KB]: 6140
% 0.15/0.43  % (4595)Time elapsed: 0.007 s
% 0.15/0.43  % (4595)------------------------------
% 0.15/0.43  % (4595)------------------------------
% 0.22/0.43  % (4583)Success in time 0.069 s
%------------------------------------------------------------------------------
