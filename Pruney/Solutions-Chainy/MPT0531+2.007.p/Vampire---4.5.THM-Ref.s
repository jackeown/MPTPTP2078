%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  73 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :  107 ( 163 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f34,f40,f47,f91,f170,f306])).

fof(f306,plain,
    ( ~ spl3_3
    | spl3_25 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl3_3
    | spl3_25 ),
    inference(subsumption_resolution,[],[f304,f33])).

fof(f33,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f304,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_25 ),
    inference(resolution,[],[f167,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f167,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl3_25
  <=> v1_relat_1(k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f170,plain,
    ( ~ spl3_25
    | spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f169,f88,f21,f165])).

fof(f21,plain,
    ( spl3_1
  <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f88,plain,
    ( spl3_13
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f169,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | spl3_1
    | ~ spl3_13 ),
    inference(global_subsumption,[],[f163])).

fof(f163,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f151,f23])).

fof(f23,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f151,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ spl3_13 ),
    inference(superposition,[],[f17,f90])).

fof(f90,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f91,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f84,f45,f26,f88])).

fof(f26,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(X0,sK2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f84,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f46,f28])).

fof(f28,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(X0,sK2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f47,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f41,f38,f45])).

fof(f38,plain,
    ( spl3_4
  <=> ! [X1,X0] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(X0,sK2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_4 ),
    inference(superposition,[],[f39,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f39,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f40,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f35,f31,f38])).

fof(f35,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f19,f33])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(f34,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f31])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

fof(f29,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f21])).

fof(f15,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (16988)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (16988)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f307,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f24,f29,f34,f40,f47,f91,f170,f306])).
% 0.21/0.43  fof(f306,plain,(
% 0.21/0.43    ~spl3_3 | spl3_25),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f305])).
% 0.21/0.43  fof(f305,plain,(
% 0.21/0.43    $false | (~spl3_3 | spl3_25)),
% 0.21/0.43    inference(subsumption_resolution,[],[f304,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f304,plain,(
% 0.21/0.43    ~v1_relat_1(sK2) | spl3_25),
% 0.21/0.43    inference(resolution,[],[f167,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.43  fof(f167,plain,(
% 0.21/0.43    ~v1_relat_1(k8_relat_1(sK1,sK2)) | spl3_25),
% 0.21/0.43    inference(avatar_component_clause,[],[f165])).
% 0.21/0.43  fof(f165,plain,(
% 0.21/0.43    spl3_25 <=> v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.43  fof(f170,plain,(
% 0.21/0.43    ~spl3_25 | spl3_1 | ~spl3_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f169,f88,f21,f165])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    spl3_1 <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    spl3_13 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.43  fof(f169,plain,(
% 0.21/0.43    ~v1_relat_1(k8_relat_1(sK1,sK2)) | (spl3_1 | ~spl3_13)),
% 0.21/0.43    inference(global_subsumption,[],[f163])).
% 0.21/0.43  fof(f163,plain,(
% 0.21/0.43    ~v1_relat_1(k8_relat_1(sK1,sK2)) | (spl3_1 | ~spl3_13)),
% 0.21/0.43    inference(subsumption_resolution,[],[f151,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f21])).
% 0.21/0.43  fof(f151,plain,(
% 0.21/0.43    r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~spl3_13),
% 0.21/0.43    inference(superposition,[],[f17,f90])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | ~spl3_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f88])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    spl3_13 | ~spl3_2 | ~spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f84,f45,f26,f88])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl3_5 <=> ! [X1,X0] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(X0,sK2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | (~spl3_2 | ~spl3_5)),
% 0.21/0.43    inference(resolution,[],[f46,f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f26])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(X0,sK2)) ) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f45])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl3_5 | ~spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f41,f38,f45])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl3_4 <=> ! [X1,X0] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(X0,sK2) | ~r1_tarski(X0,X1)) ) | ~spl3_4),
% 0.21/0.43    inference(superposition,[],[f39,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)) ) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f38])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl3_4 | ~spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f31,f38])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)) ) | ~spl3_3),
% 0.21/0.43    inference(resolution,[],[f19,f33])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f13,f31])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    v1_relat_1(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.43    inference(flattening,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f14,f26])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f15,f21])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (16988)------------------------------
% 0.21/0.43  % (16988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (16988)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (16988)Memory used [KB]: 10746
% 0.21/0.43  % (16988)Time elapsed: 0.012 s
% 0.21/0.43  % (16988)------------------------------
% 0.21/0.43  % (16988)------------------------------
% 0.21/0.43  % (16993)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (16986)Success in time 0.079 s
%------------------------------------------------------------------------------
