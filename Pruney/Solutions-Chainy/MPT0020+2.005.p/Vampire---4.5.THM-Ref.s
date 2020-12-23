%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  75 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :  104 ( 163 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f31,f36,f43,f47,f61,f80,f126])).

fof(f126,plain,
    ( ~ spl4_4
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f118,f78])).

fof(f78,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(X0,sK0),k2_xboole_0(sK1,X0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_11
  <=> ! [X0] : r1_tarski(k2_xboole_0(X0,sK0),k2_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f118,plain,
    ( ~ r1_tarski(k2_xboole_0(sK3,sK0),k2_xboole_0(sK1,sK3))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f59,f35])).

fof(f35,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_xboole_0(sK0,sK2),X0)
        | ~ r1_tarski(X0,k2_xboole_0(sK1,sK3)) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_4
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK3))
        | ~ r1_tarski(k2_xboole_0(sK0,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f59,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(sK3,X0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_8
  <=> ! [X0] : r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f80,plain,
    ( spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f69,f45,f77])).

fof(f45,plain,
    ( spl4_6
  <=> ! [X1] : r1_tarski(k2_xboole_0(sK0,X1),k2_xboole_0(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f69,plain,
    ( ! [X1] : r1_tarski(k2_xboole_0(X1,sK0),k2_xboole_0(sK1,X1))
    | ~ spl4_6 ),
    inference(superposition,[],[f46,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f46,plain,
    ( ! [X1] : r1_tarski(k2_xboole_0(sK0,X1),k2_xboole_0(sK1,X1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f61,plain,
    ( spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f50,f41,f58])).

fof(f41,plain,
    ( spl4_5
  <=> ! [X0] : r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f50,plain,
    ( ! [X1] : r1_tarski(k2_xboole_0(X1,sK2),k2_xboole_0(sK3,X1))
    | ~ spl4_5 ),
    inference(superposition,[],[f42,f14])).

fof(f42,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK3,X0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f47,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f38,f28,f45])).

fof(f28,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f38,plain,
    ( ! [X1] : r1_tarski(k2_xboole_0(sK0,X1),k2_xboole_0(sK1,X1))
    | ~ spl4_3 ),
    inference(resolution,[],[f15,f30])).

fof(f30,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f43,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f37,f23,f41])).

fof(f23,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f37,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK3,X0))
    | ~ spl4_2 ),
    inference(resolution,[],[f15,f25])).

fof(f25,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f36,plain,
    ( spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f32,f18,f34])).

fof(f18,plain,
    ( spl4_1
  <=> r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f32,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK3))
        | ~ r1_tarski(k2_xboole_0(sK0,sK2),X0) )
    | spl4_1 ),
    inference(resolution,[],[f16,f20])).

fof(f20,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f31,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f11,f28])).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f26,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f12,f23])).

fof(f12,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f13,f18])).

fof(f13,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:44:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (1210482689)
% 0.14/0.37  ipcrm: permission denied for id (1210548227)
% 0.14/0.37  ipcrm: permission denied for id (1210580998)
% 0.14/0.38  ipcrm: permission denied for id (1210646542)
% 0.14/0.40  ipcrm: permission denied for id (1210744868)
% 0.14/0.41  ipcrm: permission denied for id (1210908713)
% 0.21/0.41  ipcrm: permission denied for id (1210941484)
% 0.21/0.43  ipcrm: permission denied for id (1211007032)
% 0.21/0.46  ipcrm: permission denied for id (1211301968)
% 0.21/0.46  ipcrm: permission denied for id (1211334737)
% 0.21/0.46  ipcrm: permission denied for id (1211367506)
% 0.21/0.46  ipcrm: permission denied for id (1211400277)
% 0.21/0.46  ipcrm: permission denied for id (1211433047)
% 0.21/0.47  ipcrm: permission denied for id (1211465817)
% 0.21/0.58  % (7155)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.58  % (7145)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.59  % (7145)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f140,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(avatar_sat_refutation,[],[f21,f26,f31,f36,f43,f47,f61,f80,f126])).
% 0.21/0.59  fof(f126,plain,(
% 0.21/0.59    ~spl4_4 | ~spl4_8 | ~spl4_11),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.59  fof(f125,plain,(
% 0.21/0.59    $false | (~spl4_4 | ~spl4_8 | ~spl4_11)),
% 0.21/0.59    inference(subsumption_resolution,[],[f118,f78])).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK0),k2_xboole_0(sK1,X0))) ) | ~spl4_11),
% 0.21/0.59    inference(avatar_component_clause,[],[f77])).
% 0.21/0.59  fof(f77,plain,(
% 0.21/0.59    spl4_11 <=> ! [X0] : r1_tarski(k2_xboole_0(X0,sK0),k2_xboole_0(sK1,X0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.59  fof(f118,plain,(
% 0.21/0.59    ~r1_tarski(k2_xboole_0(sK3,sK0),k2_xboole_0(sK1,sK3)) | (~spl4_4 | ~spl4_8)),
% 0.21/0.59    inference(resolution,[],[f59,f35])).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,sK2),X0) | ~r1_tarski(X0,k2_xboole_0(sK1,sK3))) ) | ~spl4_4),
% 0.21/0.59    inference(avatar_component_clause,[],[f34])).
% 0.21/0.59  fof(f34,plain,(
% 0.21/0.59    spl4_4 <=> ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK3)) | ~r1_tarski(k2_xboole_0(sK0,sK2),X0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.59  fof(f59,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(sK3,X0))) ) | ~spl4_8),
% 0.21/0.59    inference(avatar_component_clause,[],[f58])).
% 0.21/0.59  fof(f58,plain,(
% 0.21/0.59    spl4_8 <=> ! [X0] : r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(sK3,X0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.59  fof(f80,plain,(
% 0.21/0.59    spl4_11 | ~spl4_6),
% 0.21/0.59    inference(avatar_split_clause,[],[f69,f45,f77])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    spl4_6 <=> ! [X1] : r1_tarski(k2_xboole_0(sK0,X1),k2_xboole_0(sK1,X1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.59  fof(f69,plain,(
% 0.21/0.59    ( ! [X1] : (r1_tarski(k2_xboole_0(X1,sK0),k2_xboole_0(sK1,X1))) ) | ~spl4_6),
% 0.21/0.59    inference(superposition,[],[f46,f14])).
% 0.21/0.59  fof(f14,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ( ! [X1] : (r1_tarski(k2_xboole_0(sK0,X1),k2_xboole_0(sK1,X1))) ) | ~spl4_6),
% 0.21/0.59    inference(avatar_component_clause,[],[f45])).
% 0.21/0.59  fof(f61,plain,(
% 0.21/0.59    spl4_8 | ~spl4_5),
% 0.21/0.59    inference(avatar_split_clause,[],[f50,f41,f58])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    spl4_5 <=> ! [X0] : r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK3,X0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X1] : (r1_tarski(k2_xboole_0(X1,sK2),k2_xboole_0(sK3,X1))) ) | ~spl4_5),
% 0.21/0.59    inference(superposition,[],[f42,f14])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK3,X0))) ) | ~spl4_5),
% 0.21/0.59    inference(avatar_component_clause,[],[f41])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    spl4_6 | ~spl4_3),
% 0.21/0.59    inference(avatar_split_clause,[],[f38,f28,f45])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    ( ! [X1] : (r1_tarski(k2_xboole_0(sK0,X1),k2_xboole_0(sK1,X1))) ) | ~spl4_3),
% 0.21/0.59    inference(resolution,[],[f15,f30])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.21/0.59    inference(avatar_component_clause,[],[f28])).
% 0.21/0.59  fof(f15,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    spl4_5 | ~spl4_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f37,f23,f41])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    spl4_2 <=> r1_tarski(sK2,sK3)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK3,X0))) ) | ~spl4_2),
% 0.21/0.59    inference(resolution,[],[f15,f25])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.21/0.59    inference(avatar_component_clause,[],[f23])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    spl4_4 | spl4_1),
% 0.21/0.59    inference(avatar_split_clause,[],[f32,f18,f34])).
% 0.21/0.59  fof(f18,plain,(
% 0.21/0.59    spl4_1 <=> r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK3)) | ~r1_tarski(k2_xboole_0(sK0,sK2),X0)) ) | spl4_1),
% 0.21/0.59    inference(resolution,[],[f16,f20])).
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) | spl4_1),
% 0.21/0.59    inference(avatar_component_clause,[],[f18])).
% 0.21/0.59  fof(f16,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.59    inference(flattening,[],[f9])).
% 0.21/0.59  fof(f9,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.59    inference(ennf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    spl4_3),
% 0.21/0.59    inference(avatar_split_clause,[],[f11,f28])).
% 0.21/0.59  fof(f11,plain,(
% 0.21/0.59    r1_tarski(sK0,sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,plain,(
% 0.21/0.59    ? [X0,X1,X2,X3] : (~r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.21/0.59    inference(flattening,[],[f6])).
% 0.21/0.59  fof(f6,plain,(
% 0.21/0.59    ? [X0,X1,X2,X3] : (~r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.21/0.59    inference(ennf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,negated_conjecture,(
% 0.21/0.59    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.21/0.59    inference(negated_conjecture,[],[f4])).
% 0.21/0.59  fof(f4,conjecture,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    spl4_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f12,f23])).
% 0.21/0.59  fof(f12,plain,(
% 0.21/0.59    r1_tarski(sK2,sK3)),
% 0.21/0.59    inference(cnf_transformation,[],[f7])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ~spl4_1),
% 0.21/0.59    inference(avatar_split_clause,[],[f13,f18])).
% 0.21/0.59  fof(f13,plain,(
% 0.21/0.59    ~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3))),
% 0.21/0.59    inference(cnf_transformation,[],[f7])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (7145)------------------------------
% 0.21/0.59  % (7145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (7145)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (7145)Memory used [KB]: 10618
% 0.21/0.59  % (7145)Time elapsed: 0.007 s
% 0.21/0.59  % (7145)------------------------------
% 0.21/0.59  % (7145)------------------------------
% 0.21/0.59  % (7010)Success in time 0.233 s
%------------------------------------------------------------------------------
