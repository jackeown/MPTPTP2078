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
% DateTime   : Thu Dec  3 12:50:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  119 ( 187 expanded)
%              Number of equality atoms :   23 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f35,f40,f47,f53,f57,f60])).

fof(f60,plain,
    ( spl2_2
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f58,f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK0
    | spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_6 ),
    inference(resolution,[],[f46,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f46,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f57,plain,
    ( spl2_5
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl2_5
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f55,f43])).

fof(f43,plain,
    ( ~ r1_xboole_0(sK0,k2_relat_1(sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_5
  <=> r1_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f55,plain,
    ( r1_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_7 ),
    inference(resolution,[],[f52,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f52,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_7
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f53,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f49,f38,f24,f51])).

fof(f24,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f38,plain,
    ( spl2_4
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f49,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f27,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f27,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k10_relat_1(sK1,X0)
        | r1_xboole_0(k2_relat_1(sK1),X0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

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

fof(f25,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f47,plain,
    ( ~ spl2_5
    | spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f36,f33,f45,f42])).

fof(f33,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f36,plain,
    ( v1_xboole_0(sK0)
    | ~ r1_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f34,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f34,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f40,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f35,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f14,f24])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:12 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.22/0.45  % (2898)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.46  % (2885)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.46  % (2885)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f26,f31,f35,f40,f47,f53,f57,f60])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    spl2_2 | ~spl2_6),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f59])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    $false | (spl2_2 | ~spl2_6)),
% 0.22/0.46    inference(subsumption_resolution,[],[f58,f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    k1_xboole_0 != sK0 | spl2_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    spl2_2 <=> k1_xboole_0 = sK0),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    k1_xboole_0 = sK0 | ~spl2_6),
% 0.22/0.46    inference(resolution,[],[f46,f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    v1_xboole_0(sK0) | ~spl2_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f45])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    spl2_6 <=> v1_xboole_0(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    spl2_5 | ~spl2_7),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f56])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    $false | (spl2_5 | ~spl2_7)),
% 0.22/0.46    inference(subsumption_resolution,[],[f55,f43])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    ~r1_xboole_0(sK0,k2_relat_1(sK1)) | spl2_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f42])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    spl2_5 <=> r1_xboole_0(sK0,k2_relat_1(sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    r1_xboole_0(sK0,k2_relat_1(sK1)) | ~spl2_7),
% 0.22/0.46    inference(resolution,[],[f52,f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl2_7),
% 0.22/0.46    inference(avatar_component_clause,[],[f51])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    spl2_7 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    spl2_7 | ~spl2_1 | ~spl2_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f49,f38,f24,f51])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    spl2_1 <=> v1_relat_1(sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    spl2_4 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    r1_xboole_0(k2_relat_1(sK1),sK0) | (~spl2_1 | ~spl2_4)),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f48])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),sK0) | (~spl2_1 | ~spl2_4)),
% 0.22/0.46    inference(superposition,[],[f27,f39])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl2_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f38])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | r1_xboole_0(k2_relat_1(sK1),X0)) ) | ~spl2_1),
% 0.22/0.46    inference(resolution,[],[f25,f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    v1_relat_1(sK1) | ~spl2_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f24])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    ~spl2_5 | spl2_6 | ~spl2_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f36,f33,f45,f42])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    spl2_3 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    v1_xboole_0(sK0) | ~r1_xboole_0(sK0,k2_relat_1(sK1)) | ~spl2_3),
% 0.22/0.46    inference(resolution,[],[f34,f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_xboole_0(X1) | ~r1_xboole_0(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.46    inference(flattening,[],[f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl2_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f33])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    spl2_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f17,f38])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.22/0.46    inference(flattening,[],[f7])).
% 0.22/0.46  fof(f7,plain,(
% 0.22/0.46    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.22/0.46    inference(negated_conjecture,[],[f5])).
% 0.22/0.46  fof(f5,conjecture,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    spl2_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f16,f33])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.46    inference(cnf_transformation,[],[f8])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ~spl2_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f15,f29])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    k1_xboole_0 != sK0),
% 0.22/0.46    inference(cnf_transformation,[],[f8])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    spl2_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f14,f24])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    v1_relat_1(sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f8])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (2885)------------------------------
% 0.22/0.46  % (2885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (2885)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (2885)Memory used [KB]: 6140
% 0.22/0.46  % (2885)Time elapsed: 0.046 s
% 0.22/0.46  % (2885)------------------------------
% 0.22/0.46  % (2885)------------------------------
% 0.22/0.46  % (2884)Success in time 0.104 s
%------------------------------------------------------------------------------
