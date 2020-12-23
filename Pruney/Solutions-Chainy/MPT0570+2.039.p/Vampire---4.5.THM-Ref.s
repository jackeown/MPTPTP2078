%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  83 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 239 expanded)
%              Number of equality atoms :   37 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f45,f51,f63,f71,f126])).

fof(f126,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | spl2_7 ),
    inference(subsumption_resolution,[],[f124,f44])).

fof(f44,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f124,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_1
    | spl2_7 ),
    inference(subsumption_resolution,[],[f116,f69])).

fof(f69,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_7
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f116,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f20,f29])).

fof(f29,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f71,plain,
    ( ~ spl2_7
    | spl2_6 ),
    inference(avatar_split_clause,[],[f65,f58,f67])).

fof(f58,plain,
    ( spl2_6
  <=> r1_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f65,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl2_6 ),
    inference(resolution,[],[f60,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f60,plain,
    ( ~ r1_xboole_0(sK0,k2_relat_1(sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f63,plain,
    ( ~ spl2_6
    | spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f62,f48,f37,f58])).

fof(f37,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f48,plain,
    ( spl2_5
  <=> sK0 = k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f62,plain,
    ( ~ r1_xboole_0(sK0,k2_relat_1(sK1))
    | spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f55,f39])).

fof(f39,plain,
    ( k1_xboole_0 != sK0
    | spl2_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f55,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_5 ),
    inference(superposition,[],[f50,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f50,plain,
    ( sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f51,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f46,f32,f48])).

fof(f32,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f46,plain,
    ( sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f34,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    & r1_tarski(sK0,k2_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK1,sK0)
      & r1_tarski(sK0,k2_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f40,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f19,f27])).

fof(f19,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (24571)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.42  % (24571)Refutation not found, incomplete strategy% (24571)------------------------------
% 0.21/0.42  % (24571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (24571)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (24571)Memory used [KB]: 10490
% 0.21/0.42  % (24571)Time elapsed: 0.004 s
% 0.21/0.42  % (24571)------------------------------
% 0.21/0.42  % (24571)------------------------------
% 0.21/0.46  % (24567)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (24567)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f30,f35,f40,f45,f51,f63,f71,f126])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    ~spl2_1 | ~spl2_4 | spl2_7),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    $false | (~spl2_1 | ~spl2_4 | spl2_7)),
% 0.21/0.46    inference(subsumption_resolution,[],[f124,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl2_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl2_4 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    ~v1_relat_1(sK1) | (~spl2_1 | spl2_7)),
% 0.21/0.46    inference(subsumption_resolution,[],[f116,f69])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl2_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl2_7 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    r1_xboole_0(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f115])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.46    inference(superposition,[],[f20,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    spl2_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ~spl2_7 | spl2_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f65,f58,f67])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl2_6 <=> r1_xboole_0(sK0,k2_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl2_6),
% 0.21/0.46    inference(resolution,[],[f60,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ~r1_xboole_0(sK0,k2_relat_1(sK1)) | spl2_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f58])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ~spl2_6 | spl2_3 | ~spl2_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f62,f48,f37,f58])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl2_3 <=> k1_xboole_0 = sK0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl2_5 <=> sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ~r1_xboole_0(sK0,k2_relat_1(sK1)) | (spl2_3 | ~spl2_5)),
% 0.21/0.46    inference(subsumption_resolution,[],[f55,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    k1_xboole_0 != sK0 | spl2_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f37])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    k1_xboole_0 = sK0 | ~r1_xboole_0(sK0,k2_relat_1(sK1)) | ~spl2_5),
% 0.21/0.46    inference(superposition,[],[f50,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    sK0 = k3_xboole_0(sK0,k2_relat_1(sK1)) | ~spl2_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl2_5 | ~spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f46,f32,f48])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    spl2_2 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    sK0 = k3_xboole_0(sK0,k2_relat_1(sK1)) | ~spl2_2),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f34,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f32])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    spl2_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f42])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ~spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    k1_xboole_0 != sK0),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f32])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f27])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (24567)------------------------------
% 0.21/0.46  % (24567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (24567)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (24567)Memory used [KB]: 10618
% 0.21/0.46  % (24567)Time elapsed: 0.049 s
% 0.21/0.46  % (24567)------------------------------
% 0.21/0.46  % (24567)------------------------------
% 0.21/0.46  % (24550)Success in time 0.104 s
%------------------------------------------------------------------------------
