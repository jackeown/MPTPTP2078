%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  38 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 (  88 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f25,f29,f33,f43])).

fof(f43,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f42])).

fof(f42,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f24,f35])).

fof(f35,plain,
    ( ! [X0] : v1_finset_1(k3_xboole_0(sK0,X0))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f19,f28,f32])).

fof(f32,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_finset_1(X1)
        | v1_finset_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( v1_finset_1(X0)
        | ~ v1_finset_1(X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f28,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_3
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f19,plain,
    ( v1_finset_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl2_1
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f24,plain,
    ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl2_2
  <=> v1_finset_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f33,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

fof(f29,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f25,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f12,f22])).

fof(f12,plain,(
    ~ v1_finset_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k3_xboole_0(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k3_xboole_0(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_finset_1)).

fof(f20,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f11,f17])).

fof(f11,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (9082)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (9082)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f20,f25,f29,f33,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    $false | (~spl2_1 | spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.44    inference(subsumption_resolution,[],[f24,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0] : (v1_finset_1(k3_xboole_0(sK0,X0))) ) | (~spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f19,f28,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_finset_1(X1) | v1_finset_1(X0)) ) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    spl2_4 <=> ! [X1,X0] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    spl2_3 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    v1_finset_1(sK0) | ~spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    spl2_1 <=> v1_finset_1(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ~v1_finset_1(k3_xboole_0(sK0,sK1)) | spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    spl2_2 <=> v1_finset_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f31])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f13,f27])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ~spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f12,f22])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ~v1_finset_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ~v1_finset_1(k3_xboole_0(sK0,sK1)) & v1_finset_1(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1] : (~v1_finset_1(k3_xboole_0(X0,X1)) & v1_finset_1(X0)) => (~v1_finset_1(k3_xboole_0(sK0,sK1)) & v1_finset_1(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ? [X0,X1] : (~v1_finset_1(k3_xboole_0(X0,X1)) & v1_finset_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.21/0.44    inference(negated_conjecture,[],[f4])).
% 0.21/0.44  fof(f4,conjecture,(
% 0.21/0.44    ! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_finset_1)).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f11,f17])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    v1_finset_1(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (9082)------------------------------
% 0.21/0.44  % (9082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (9082)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (9082)Memory used [KB]: 6012
% 0.21/0.44  % (9082)Time elapsed: 0.045 s
% 0.21/0.44  % (9082)------------------------------
% 0.21/0.44  % (9082)------------------------------
% 0.21/0.44  % (9071)Success in time 0.086 s
%------------------------------------------------------------------------------
