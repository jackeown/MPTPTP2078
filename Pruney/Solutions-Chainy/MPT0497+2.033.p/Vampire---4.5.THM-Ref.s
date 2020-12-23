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
% DateTime   : Thu Dec  3 12:48:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 121 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  186 ( 303 expanded)
%              Number of equality atoms :   54 (  88 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f69,f82,f119,f148,f168])).

fof(f168,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | spl2_6 ),
    inference(subsumption_resolution,[],[f166,f80])).

fof(f80,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_6
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f166,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f165,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f165,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f163,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f163,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k1_xboole_0)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f100,f64])).

fof(f64,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_4
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f100,plain,
    ( ! [X0] : r1_xboole_0(X0,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))))
    | ~ spl2_1 ),
    inference(superposition,[],[f72,f89])).

fof(f89,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f49,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f49,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f72,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))) ),
    inference(unit_resulting_resolution,[],[f44,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X1) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f42])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f148,plain,
    ( ~ spl2_1
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f95,f144])).

fof(f144,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f27,f136])).

fof(f136,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f74,f118])).

fof(f118,plain,
    ( k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl2_7
  <=> k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f74,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f49,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f27,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f95,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f81,f41])).

fof(f81,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f119,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f108,f79,f47,f116])).

fof(f108,plain,
    ( k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f49,f81,f87])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2)
      | ~ r1_xboole_0(X1,k1_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f84,f30])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f84,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X2))
      | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f34,f33])).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
      | k1_xboole_0 = k5_relat_1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
           => k1_xboole_0 = k5_relat_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

fof(f82,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f70,f66,f79])).

fof(f66,plain,
    ( spl2_5
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f70,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f68,f41])).

fof(f68,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f69,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f26,f66,f62])).

fof(f26,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f50,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f25,f47])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:42 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.43  % (7420)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.44  % (7420)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f173,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f50,f55,f69,f82,f119,f148,f168])).
% 0.22/0.44  fof(f168,plain,(
% 0.22/0.44    ~spl2_1 | ~spl2_2 | ~spl2_4 | spl2_6),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f167])).
% 0.22/0.44  fof(f167,plain,(
% 0.22/0.44    $false | (~spl2_1 | ~spl2_2 | ~spl2_4 | spl2_6)),
% 0.22/0.44    inference(subsumption_resolution,[],[f166,f80])).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,k1_relat_1(sK1)) | spl2_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f79])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    spl2_6 <=> r1_xboole_0(sK0,k1_relat_1(sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.44  fof(f166,plain,(
% 0.22/0.44    r1_xboole_0(sK0,k1_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_4)),
% 0.22/0.44    inference(forward_demodulation,[],[f165,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.44  fof(f165,plain,(
% 0.22/0.44    r1_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k1_xboole_0)) | (~spl2_1 | ~spl2_2 | ~spl2_4)),
% 0.22/0.44    inference(forward_demodulation,[],[f163,f54])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f52])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl2_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.44  fof(f163,plain,(
% 0.22/0.44    r1_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k1_xboole_0))) | (~spl2_1 | ~spl2_4)),
% 0.22/0.44    inference(superposition,[],[f100,f64])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f62])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    spl2_4 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    ( ! [X0] : (r1_xboole_0(X0,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))))) ) | ~spl2_1),
% 0.22/0.44    inference(superposition,[],[f72,f89])).
% 0.22/0.44  fof(f89,plain,(
% 0.22/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))) ) | ~spl2_1),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f49,f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f40,f42])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f36,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    v1_relat_1(sK1) | ~spl2_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f47])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    spl2_1 <=> v1_relat_1(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0))))) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f44,f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f35,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f38,f42])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.44  fof(f148,plain,(
% 0.22/0.44    ~spl2_1 | ~spl2_6 | ~spl2_7),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f147])).
% 0.22/0.44  fof(f147,plain,(
% 0.22/0.44    $false | (~spl2_1 | ~spl2_6 | ~spl2_7)),
% 0.22/0.44    inference(subsumption_resolution,[],[f95,f144])).
% 0.22/0.44  fof(f144,plain,(
% 0.22/0.44    ~r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_1 | ~spl2_7)),
% 0.22/0.44    inference(subsumption_resolution,[],[f27,f136])).
% 0.22/0.44  fof(f136,plain,(
% 0.22/0.44    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_1 | ~spl2_7)),
% 0.22/0.44    inference(superposition,[],[f74,f118])).
% 0.22/0.44  fof(f118,plain,(
% 0.22/0.44    k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1) | ~spl2_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f116])).
% 0.22/0.44  fof(f116,plain,(
% 0.22/0.44    spl2_7 <=> k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_1),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f49,f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.44    inference(nnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.44    inference(negated_conjecture,[],[f13])).
% 0.22/0.44  fof(f13,conjecture,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_6),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f81,f41])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f79])).
% 0.22/0.44  fof(f119,plain,(
% 0.22/0.44    spl2_7 | ~spl2_1 | ~spl2_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f108,f79,f47,f116])).
% 0.22/0.44  fof(f108,plain,(
% 0.22/0.44    k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1) | (~spl2_1 | ~spl2_6)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f49,f81,f87])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    ( ! [X2,X1] : (~v1_relat_1(X2) | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2) | ~r1_xboole_0(X1,k1_relat_1(X2))) )),
% 0.22/0.44    inference(subsumption_resolution,[],[f84,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    ( ! [X2,X1] : (~r1_xboole_0(X1,k1_relat_1(X2)) | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.44    inference(superposition,[],[f34,f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | k1_xboole_0 = k5_relat_1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) => k1_xboole_0 = k5_relat_1(X0,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    spl2_6 | ~spl2_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f70,f66,f79])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    spl2_5 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_5),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f68,f41])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f66])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    spl2_4 | spl2_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f66,f62])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    spl2_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f28,f52])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl2_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f25,f47])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    v1_relat_1(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (7420)------------------------------
% 0.22/0.44  % (7420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (7420)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (7420)Memory used [KB]: 10746
% 0.22/0.44  % (7420)Time elapsed: 0.034 s
% 0.22/0.44  % (7420)------------------------------
% 0.22/0.44  % (7420)------------------------------
% 0.22/0.45  % (7404)Success in time 0.086 s
%------------------------------------------------------------------------------
