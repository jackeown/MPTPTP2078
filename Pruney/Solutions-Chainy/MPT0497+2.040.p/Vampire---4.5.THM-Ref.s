%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 125 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  194 ( 320 expanded)
%              Number of equality atoms :   50 (  86 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f68,f75,f88,f98,f194,f207,f215,f234])).

fof(f234,plain,
    ( ~ spl2_5
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(global_subsumption,[],[f26,f67,f230])).

fof(f230,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(superposition,[],[f87,f193])).

fof(f193,plain,
    ( k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl2_21
  <=> k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f87,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_7
  <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f67,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_5
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f26,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
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

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f215,plain,(
    spl2_22 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl2_22 ),
    inference(unit_resulting_resolution,[],[f30,f206,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f206,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl2_22 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl2_22
  <=> r1_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f207,plain,
    ( ~ spl2_22
    | ~ spl2_2
    | ~ spl2_4
    | spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f200,f96,f65,f61,f47,f204])).

fof(f47,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f61,plain,
    ( spl2_4
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f96,plain,
    ( spl2_8
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f200,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl2_2
    | ~ spl2_4
    | spl2_5
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f199,f49])).

fof(f49,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f199,plain,
    ( ~ r1_xboole_0(k1_relat_1(k1_xboole_0),sK0)
    | ~ spl2_4
    | spl2_5
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f198,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f198,plain,
    ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)
    | spl2_5
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f196,f97])).

fof(f97,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f196,plain,
    ( ~ r1_xboole_0(k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)),sK0)
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f66,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f66,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f194,plain,
    ( spl2_21
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f179,f72,f42,f191])).

fof(f42,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f72,plain,
    ( spl2_6
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f179,plain,
    ( k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f44,f74,f108])).

fof(f108,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X1,k1_relat_1(X2))
      | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f107,f32])).

fof(f32,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f107,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(k2_relat_1(k6_relat_1(X1)),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k5_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
           => k1_xboole_0 = k5_relat_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

fof(f74,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f44,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f98,plain,
    ( spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f89,f42,f96])).

fof(f89,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f44,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f88,plain,
    ( spl2_7
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f81,f42,f86])).

fof(f81,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f44,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f75,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f69,f65,f72])).

fof(f69,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f67,f37])).

fof(f68,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f25,f65,f61])).

fof(f25,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f47])).

fof(f27,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f45,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (19703)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.43  % (19703)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f235,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f45,f50,f68,f75,f88,f98,f194,f207,f215,f234])).
% 0.21/0.43  fof(f234,plain,(
% 0.21/0.43    ~spl2_5 | ~spl2_7 | ~spl2_21),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.43  fof(f233,plain,(
% 0.21/0.43    $false | (~spl2_5 | ~spl2_7 | ~spl2_21)),
% 0.21/0.43    inference(global_subsumption,[],[f26,f67,f230])).
% 0.21/0.43  fof(f230,plain,(
% 0.21/0.43    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_7 | ~spl2_21)),
% 0.21/0.43    inference(superposition,[],[f87,f193])).
% 0.21/0.43  fof(f193,plain,(
% 0.21/0.43    k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1) | ~spl2_21),
% 0.21/0.43    inference(avatar_component_clause,[],[f191])).
% 0.21/0.43  fof(f191,plain,(
% 0.21/0.43    spl2_21 <=> k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f86])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    spl2_7 <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f65])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl2_5 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.43    inference(negated_conjecture,[],[f11])).
% 0.21/0.43  fof(f11,conjecture,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.43  fof(f215,plain,(
% 0.21/0.43    spl2_22),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.43  fof(f211,plain,(
% 0.21/0.43    $false | spl2_22),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f30,f206,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.43  fof(f206,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_xboole_0,sK0) | spl2_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f204])).
% 0.21/0.43  fof(f204,plain,(
% 0.21/0.43    spl2_22 <=> r1_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.43  fof(f207,plain,(
% 0.21/0.43    ~spl2_22 | ~spl2_2 | ~spl2_4 | spl2_5 | ~spl2_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f200,f96,f65,f61,f47,f204])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl2_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    spl2_4 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    spl2_8 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.43  fof(f200,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_xboole_0,sK0) | (~spl2_2 | ~spl2_4 | spl2_5 | ~spl2_8)),
% 0.21/0.43    inference(forward_demodulation,[],[f199,f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f47])).
% 0.21/0.43  fof(f199,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_relat_1(k1_xboole_0),sK0) | (~spl2_4 | spl2_5 | ~spl2_8)),
% 0.21/0.43    inference(forward_demodulation,[],[f198,f63])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f61])).
% 0.21/0.43  fof(f198,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) | (spl2_5 | ~spl2_8)),
% 0.21/0.43    inference(forward_demodulation,[],[f196,f97])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | ~spl2_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f96])).
% 0.21/0.43  fof(f196,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)),sK0) | spl2_5),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f66,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f38,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl2_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f65])).
% 0.21/0.43  fof(f194,plain,(
% 0.21/0.43    spl2_21 | ~spl2_1 | ~spl2_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f179,f72,f42,f191])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    spl2_6 <=> r1_xboole_0(sK0,k1_relat_1(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.43  fof(f179,plain,(
% 0.21/0.43    k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1) | (~spl2_1 | ~spl2_6)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f44,f74,f108])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    ( ! [X2,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X1,k1_relat_1(X2)) | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2)) )),
% 0.21/0.43    inference(forward_demodulation,[],[f107,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    ( ! [X2,X1] : (~r1_xboole_0(k2_relat_1(k6_relat_1(X1)),k1_relat_1(X2)) | ~v1_relat_1(X2) | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2)) )),
% 0.21/0.43    inference(resolution,[],[f33,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_xboole_0 = k5_relat_1(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) => k1_xboole_0 = k5_relat_1(X0,X1))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f72])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f42])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    spl2_8 | ~spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f89,f42,f96])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | ~spl2_1),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f44,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f36,f34])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    spl2_7 | ~spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f81,f42,f86])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_1),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f44,f35])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl2_6 | ~spl2_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f69,f65,f72])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_5),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f67,f37])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl2_4 | spl2_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f65,f61])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f47])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f42])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    v1_relat_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (19703)------------------------------
% 0.21/0.43  % (19703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (19703)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (19703)Memory used [KB]: 10746
% 0.21/0.43  % (19703)Time elapsed: 0.031 s
% 0.21/0.43  % (19703)------------------------------
% 0.21/0.43  % (19703)------------------------------
% 0.21/0.43  % (19685)Success in time 0.079 s
%------------------------------------------------------------------------------
