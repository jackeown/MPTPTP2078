%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:13 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 111 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 ( 242 expanded)
%              Number of equality atoms :   20 (  55 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f62,f73,f86,f89])).

fof(f89,plain,
    ( ~ spl4_3
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl4_3
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f33,f49,f72,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_7
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f49,plain,
    ( r2_hidden(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,k1_relat_1(sK2))))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f20,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f86,plain,
    ( ~ spl4_3
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl4_3
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f49,f78])).

fof(f78,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK2))))
    | spl4_6 ),
    inference(superposition,[],[f75,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f21,f23,f23])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f75,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)))
    | spl4_6 ),
    inference(resolution,[],[f74,f33])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,X0) )
    | spl4_6 ),
    inference(resolution,[],[f68,f24])).

fof(f68,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_6
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f73,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | spl4_5 ),
    inference(avatar_split_clause,[],[f63,f59,f70,f66,f37])).

fof(f37,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f59,plain,
    ( spl4_5
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f63,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl4_5 ),
    inference(resolution,[],[f61,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f61,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f62,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | ~ spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f57,f52,f42,f59,f37])).

fof(f42,plain,
    ( spl4_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f52,plain,
    ( spl4_4
  <=> k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f57,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(superposition,[],[f54,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(f54,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f55,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f19,f52])).

fof(f19,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

fof(f50,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f35,f47])).

fof(f35,plain,(
    r2_hidden(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f32,f34])).

fof(f32,plain,(
    r2_hidden(sK0,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),sK1))) ),
    inference(definition_unfolding,[],[f18,f31])).

fof(f18,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:50:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.49  % (31402)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.49  % (31394)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.50  % (31402)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f90,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f62,f73,f86,f89])).
% 0.23/0.50  fof(f89,plain,(
% 0.23/0.50    ~spl4_3 | spl4_7),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f87])).
% 0.23/0.50  fof(f87,plain,(
% 0.23/0.50    $false | (~spl4_3 | spl4_7)),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f33,f49,f72,f24])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f12])).
% 0.23/0.50  fof(f12,plain,(
% 0.23/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.23/0.50  fof(f72,plain,(
% 0.23/0.50    ~r2_hidden(sK0,sK1) | spl4_7),
% 0.23/0.50    inference(avatar_component_clause,[],[f70])).
% 0.23/0.50  fof(f70,plain,(
% 0.23/0.50    spl4_7 <=> r2_hidden(sK0,sK1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.23/0.50  fof(f49,plain,(
% 0.23/0.50    r2_hidden(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,k1_relat_1(sK2)))) | ~spl4_3),
% 0.23/0.50    inference(avatar_component_clause,[],[f47])).
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    spl4_3 <=> r2_hidden(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,k1_relat_1(sK2))))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 0.23/0.50    inference(definition_unfolding,[],[f20,f31])).
% 0.23/0.50  fof(f31,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.23/0.50    inference(definition_unfolding,[],[f22,f23])).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.50  fof(f22,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f5])).
% 0.23/0.50  fof(f5,axiom,(
% 0.23/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.50  fof(f20,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.23/0.50  fof(f86,plain,(
% 0.23/0.50    ~spl4_3 | spl4_6),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f80])).
% 0.23/0.50  fof(f80,plain,(
% 0.23/0.50    $false | (~spl4_3 | spl4_6)),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f49,f78])).
% 0.23/0.50  fof(f78,plain,(
% 0.23/0.50    ( ! [X0] : (~r2_hidden(sK0,k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK2))))) ) | spl4_6),
% 0.23/0.50    inference(superposition,[],[f75,f34])).
% 0.23/0.50  fof(f34,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.23/0.50    inference(definition_unfolding,[],[f21,f23,f23])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f3])).
% 0.23/0.50  fof(f3,axiom,(
% 0.23/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.23/0.50  fof(f75,plain,(
% 0.23/0.50    ( ! [X0] : (~r2_hidden(sK0,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)))) ) | spl4_6),
% 0.23/0.50    inference(resolution,[],[f74,f33])).
% 0.23/0.50  fof(f74,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | ~r2_hidden(sK0,X0)) ) | spl4_6),
% 0.23/0.50    inference(resolution,[],[f68,f24])).
% 0.23/0.50  fof(f68,plain,(
% 0.23/0.50    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl4_6),
% 0.23/0.50    inference(avatar_component_clause,[],[f66])).
% 0.23/0.50  fof(f66,plain,(
% 0.23/0.50    spl4_6 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.23/0.50  fof(f73,plain,(
% 0.23/0.50    ~spl4_1 | ~spl4_6 | ~spl4_7 | spl4_5),
% 0.23/0.50    inference(avatar_split_clause,[],[f63,f59,f70,f66,f37])).
% 0.23/0.50  fof(f37,plain,(
% 0.23/0.50    spl4_1 <=> v1_relat_1(sK2)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.50  fof(f59,plain,(
% 0.23/0.50    spl4_5 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.23/0.50  fof(f63,plain,(
% 0.23/0.50    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl4_5),
% 0.23/0.50    inference(resolution,[],[f61,f29])).
% 0.23/0.50  fof(f29,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f13])).
% 0.23/0.50  fof(f13,plain,(
% 0.23/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.23/0.50    inference(ennf_transformation,[],[f6])).
% 0.23/0.50  fof(f6,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.23/0.50  fof(f61,plain,(
% 0.23/0.50    ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | spl4_5),
% 0.23/0.50    inference(avatar_component_clause,[],[f59])).
% 0.23/0.50  fof(f62,plain,(
% 0.23/0.50    ~spl4_1 | ~spl4_5 | ~spl4_2 | spl4_4),
% 0.23/0.50    inference(avatar_split_clause,[],[f57,f52,f42,f59,f37])).
% 0.23/0.50  fof(f42,plain,(
% 0.23/0.50    spl4_2 <=> v1_funct_1(sK2)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.50  fof(f52,plain,(
% 0.23/0.50    spl4_4 <=> k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.50  fof(f57,plain,(
% 0.23/0.50    ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~v1_relat_1(sK2) | spl4_4),
% 0.23/0.50    inference(trivial_inequality_removal,[],[f56])).
% 0.23/0.50  fof(f56,plain,(
% 0.23/0.50    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~v1_relat_1(sK2) | spl4_4),
% 0.23/0.50    inference(superposition,[],[f54,f30])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f15])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.23/0.50    inference(flattening,[],[f14])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.23/0.50    inference(ennf_transformation,[],[f7])).
% 0.23/0.50  fof(f7,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).
% 0.23/0.50  fof(f54,plain,(
% 0.23/0.50    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) | spl4_4),
% 0.23/0.50    inference(avatar_component_clause,[],[f52])).
% 0.23/0.50  fof(f55,plain,(
% 0.23/0.50    ~spl4_4),
% 0.23/0.50    inference(avatar_split_clause,[],[f19,f52])).
% 0.23/0.50  fof(f19,plain,(
% 0.23/0.50    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f11])).
% 0.23/0.50  fof(f11,plain,(
% 0.23/0.50    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.23/0.50    inference(flattening,[],[f10])).
% 0.23/0.50  fof(f10,plain,(
% 0.23/0.50    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.23/0.50    inference(ennf_transformation,[],[f9])).
% 0.23/0.50  fof(f9,negated_conjecture,(
% 0.23/0.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.23/0.50    inference(negated_conjecture,[],[f8])).
% 0.23/0.50  fof(f8,conjecture,(
% 0.23/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).
% 0.23/0.50  fof(f50,plain,(
% 0.23/0.50    spl4_3),
% 0.23/0.50    inference(avatar_split_clause,[],[f35,f47])).
% 0.23/0.50  fof(f35,plain,(
% 0.23/0.50    r2_hidden(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,k1_relat_1(sK2))))),
% 0.23/0.50    inference(forward_demodulation,[],[f32,f34])).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    r2_hidden(sK0,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),sK1)))),
% 0.23/0.50    inference(definition_unfolding,[],[f18,f31])).
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.23/0.50    inference(cnf_transformation,[],[f11])).
% 0.23/0.50  fof(f45,plain,(
% 0.23/0.50    spl4_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f17,f42])).
% 0.23/0.50  fof(f17,plain,(
% 0.23/0.50    v1_funct_1(sK2)),
% 0.23/0.50    inference(cnf_transformation,[],[f11])).
% 0.23/0.50  fof(f40,plain,(
% 0.23/0.50    spl4_1),
% 0.23/0.50    inference(avatar_split_clause,[],[f16,f37])).
% 0.23/0.50  fof(f16,plain,(
% 0.23/0.50    v1_relat_1(sK2)),
% 0.23/0.50    inference(cnf_transformation,[],[f11])).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (31402)------------------------------
% 0.23/0.50  % (31402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (31402)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (31402)Memory used [KB]: 10746
% 0.23/0.50  % (31402)Time elapsed: 0.063 s
% 0.23/0.50  % (31402)------------------------------
% 0.23/0.50  % (31402)------------------------------
% 0.23/0.51  % (31379)Success in time 0.132 s
%------------------------------------------------------------------------------
