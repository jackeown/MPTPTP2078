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
% DateTime   : Thu Dec  3 12:47:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  90 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  161 ( 268 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f56,f61,f66])).

fof(f66,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_6 ),
    inference(subsumption_resolution,[],[f64,f24])).

fof(f24,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f64,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_4
    | spl2_6 ),
    inference(subsumption_resolution,[],[f63,f34])).

fof(f34,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f63,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl2_4
    | spl2_6 ),
    inference(subsumption_resolution,[],[f62,f39])).

fof(f39,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f62,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | spl2_6 ),
    inference(resolution,[],[f55,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f55,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_6
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f61,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_5 ),
    inference(subsumption_resolution,[],[f59,f24])).

fof(f59,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_4
    | spl2_5 ),
    inference(subsumption_resolution,[],[f58,f34])).

fof(f58,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl2_4
    | spl2_5 ),
    inference(subsumption_resolution,[],[f57,f39])).

fof(f57,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | spl2_5 ),
    inference(resolution,[],[f51,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_5
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f56,plain,
    ( ~ spl2_5
    | ~ spl2_6
    | ~ spl2_1
    | spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f47,f37,f27,f22,f53,f49])).

fof(f27,plain,
    ( spl2_2
  <=> r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f47,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_1
    | spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f46,f39])).

fof(f46,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f45,f24])).

fof(f45,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X1),k3_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X1),k2_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f41,f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k2_xboole_0(X1,X2))
      | ~ r1_tarski(k2_relat_1(X0),X2)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f20,f17])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f40,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f13,f37])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f35,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f14,f32])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f15,f27])).

fof(f15,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f25,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f16,f22])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (24821)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.42  % (24821)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f56,f61,f66])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    ~spl2_1 | ~spl2_3 | ~spl2_4 | spl2_6),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f65])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    $false | (~spl2_1 | ~spl2_3 | ~spl2_4 | spl2_6)),
% 0.20/0.42    inference(subsumption_resolution,[],[f64,f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    v1_relat_1(sK0) | ~spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    spl2_1 <=> v1_relat_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    ~v1_relat_1(sK0) | (~spl2_3 | ~spl2_4 | spl2_6)),
% 0.20/0.42    inference(subsumption_resolution,[],[f63,f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    spl2_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0) | (~spl2_4 | spl2_6)),
% 0.20/0.42    inference(subsumption_resolution,[],[f62,f39])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    v1_relat_1(sK1) | ~spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    spl2_4 <=> v1_relat_1(sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0) | spl2_6),
% 0.20/0.42    inference(resolution,[],[f55,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | spl2_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f53])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl2_6 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    ~spl2_1 | ~spl2_3 | ~spl2_4 | spl2_5),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f60])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    $false | (~spl2_1 | ~spl2_3 | ~spl2_4 | spl2_5)),
% 0.20/0.42    inference(subsumption_resolution,[],[f59,f24])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    ~v1_relat_1(sK0) | (~spl2_3 | ~spl2_4 | spl2_5)),
% 0.20/0.42    inference(subsumption_resolution,[],[f58,f34])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0) | (~spl2_4 | spl2_5)),
% 0.20/0.42    inference(subsumption_resolution,[],[f57,f39])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0) | spl2_5),
% 0.20/0.42    inference(resolution,[],[f51,f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | spl2_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f49])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl2_5 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    ~spl2_5 | ~spl2_6 | ~spl2_1 | spl2_2 | ~spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f47,f37,f27,f22,f53,f49])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    spl2_2 <=> r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | (~spl2_1 | spl2_2 | ~spl2_4)),
% 0.20/0.42    inference(subsumption_resolution,[],[f46,f39])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl2_1 | spl2_2)),
% 0.20/0.42    inference(subsumption_resolution,[],[f45,f24])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | spl2_2),
% 0.20/0.42    inference(resolution,[],[f43,f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f27])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X1),k3_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k2_relat_1(X0)) | ~r1_tarski(k1_relat_1(X1),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(superposition,[],[f41,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(k3_relat_1(X0),k2_xboole_0(X1,X2)) | ~r1_tarski(k2_relat_1(X0),X2) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(superposition,[],[f20,f17])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f13,f37])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    v1_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f6])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.20/0.42    inference(negated_conjecture,[],[f4])).
% 0.20/0.42  fof(f4,conjecture,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    spl2_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f14,f32])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ~spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f27])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f22])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    v1_relat_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (24821)------------------------------
% 0.20/0.42  % (24821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (24821)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (24821)Memory used [KB]: 10618
% 0.20/0.42  % (24821)Time elapsed: 0.006 s
% 0.20/0.42  % (24821)------------------------------
% 0.20/0.42  % (24821)------------------------------
% 0.20/0.42  % (24816)Success in time 0.069 s
%------------------------------------------------------------------------------
