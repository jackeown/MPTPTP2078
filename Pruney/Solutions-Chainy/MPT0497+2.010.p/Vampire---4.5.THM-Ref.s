%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 120 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  214 ( 329 expanded)
%              Number of equality atoms :   51 (  88 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f68,f69,f74,f86,f132,f140,f172,f177])).

% (12582)Refutation not found, incomplete strategy% (12582)------------------------------
% (12582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12582)Termination reason: Refutation not found, incomplete strategy

% (12582)Memory used [KB]: 10618
% (12582)Time elapsed: 0.106 s
% (12582)------------------------------
% (12582)------------------------------
fof(f177,plain,
    ( spl2_6
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl2_6
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f53,f37,f84,f171])).

fof(f171,plain,
    ( ! [X3] :
        ( r1_xboole_0(X3,k1_relat_1(sK1))
        | ~ r1_xboole_0(X3,k1_xboole_0)
        | ~ r1_tarski(X3,sK0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl2_9
  <=> ! [X3] :
        ( ~ r1_xboole_0(X3,k1_xboole_0)
        | r1_xboole_0(X3,k1_relat_1(sK1))
        | ~ r1_tarski(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f84,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_6
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f172,plain,
    ( ~ spl2_1
    | spl2_9
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f164,f71,f61,f170,f56])).

fof(f56,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f61,plain,
    ( spl2_2
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f71,plain,
    ( spl2_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f164,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(X3,k1_xboole_0)
        | ~ r1_tarski(X3,sK0)
        | r1_xboole_0(X3,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f158,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f158,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(X3,k1_relat_1(k1_xboole_0))
        | ~ r1_tarski(X3,sK0)
        | r1_xboole_0(X3,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2 ),
    inference(superposition,[],[f97,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X2,k1_relat_1(k7_relat_1(X0,X1)))
      | ~ r1_tarski(X2,X1)
      | r1_xboole_0(X2,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f51,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f140,plain,
    ( spl2_3
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl2_3
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f85,f66,f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f66,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_3
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f85,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f132,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f58,f44,f85,f62,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r1_xboole_0(X0,k1_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r1_xboole_0(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f43,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_relat_1(k6_relat_1(X0),X1)
      | ~ r1_xboole_0(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f36,f40])).

fof(f40,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
      | k1_xboole_0 = k5_relat_1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
           => k1_xboole_0 = k5_relat_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f62,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f58,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f86,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f81,f65,f83])).

fof(f81,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f35,f67])).

fof(f67,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f74,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f41,f71])).

fof(f41,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f69,plain,
    ( ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f33,f65,f61])).

fof(f33,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
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

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f68,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f32,f65,f61])).

fof(f32,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:42:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (12595)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (12575)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (12586)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (12577)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (12574)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (12586)Refutation not found, incomplete strategy% (12586)------------------------------
% 0.21/0.52  % (12586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12578)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12586)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12586)Memory used [KB]: 1663
% 0.21/0.52  % (12586)Time elapsed: 0.051 s
% 0.21/0.52  % (12586)------------------------------
% 0.21/0.52  % (12586)------------------------------
% 0.21/0.52  % (12593)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (12573)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (12576)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (12573)Refutation not found, incomplete strategy% (12573)------------------------------
% 0.21/0.52  % (12573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12573)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12573)Memory used [KB]: 1663
% 0.21/0.52  % (12573)Time elapsed: 0.106 s
% 0.21/0.52  % (12573)------------------------------
% 0.21/0.52  % (12573)------------------------------
% 0.21/0.52  % (12582)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (12595)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f59,f68,f69,f74,f86,f132,f140,f172,f177])).
% 0.21/0.52  % (12582)Refutation not found, incomplete strategy% (12582)------------------------------
% 0.21/0.52  % (12582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12582)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12582)Memory used [KB]: 10618
% 0.21/0.52  % (12582)Time elapsed: 0.106 s
% 0.21/0.52  % (12582)------------------------------
% 0.21/0.52  % (12582)------------------------------
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    spl2_6 | ~spl2_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f173])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    $false | (spl2_6 | ~spl2_9)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f53,f37,f84,f171])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ( ! [X3] : (r1_xboole_0(X3,k1_relat_1(sK1)) | ~r1_xboole_0(X3,k1_xboole_0) | ~r1_tarski(X3,sK0)) ) | ~spl2_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f170])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    spl2_9 <=> ! [X3] : (~r1_xboole_0(X3,k1_xboole_0) | r1_xboole_0(X3,k1_relat_1(sK1)) | ~r1_tarski(X3,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ~r1_xboole_0(sK0,k1_relat_1(sK1)) | spl2_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl2_6 <=> r1_xboole_0(sK0,k1_relat_1(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ~spl2_1 | spl2_9 | ~spl2_2 | ~spl2_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f164,f71,f61,f170,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    spl2_2 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    spl2_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ( ! [X3] : (~r1_xboole_0(X3,k1_xboole_0) | ~r1_tarski(X3,sK0) | r1_xboole_0(X3,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_4)),
% 0.21/0.53    inference(forward_demodulation,[],[f158,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f71])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ( ! [X3] : (~r1_xboole_0(X3,k1_relat_1(k1_xboole_0)) | ~r1_tarski(X3,sK0) | r1_xboole_0(X3,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl2_2),
% 0.21/0.53    inference(superposition,[],[f97,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f61])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,k1_relat_1(k7_relat_1(X0,X1))) | ~r1_tarski(X2,X1) | r1_xboole_0(X2,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(superposition,[],[f51,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f38,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f45,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f34,f50])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    spl2_3 | ~spl2_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    $false | (spl2_3 | ~spl2_6)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f85,f66,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl2_3 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f83])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ~spl2_1 | spl2_2 | ~spl2_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    $false | (~spl2_1 | spl2_2 | ~spl2_6)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f58,f44,f85,f62,f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r1_xboole_0(X0,k1_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f123])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r1_xboole_0(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.53    inference(superposition,[],[f43,f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k5_relat_1(k6_relat_1(X0),X1) | ~r1_xboole_0(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.53    inference(superposition,[],[f36,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | k1_xboole_0 = k5_relat_1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) => k1_xboole_0 = k5_relat_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    k1_xboole_0 != k7_relat_1(sK1,sK0) | spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f61])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f56])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl2_6 | ~spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f81,f65,f83])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_3),
% 0.21/0.53    inference(resolution,[],[f35,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f65])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl2_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f71])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ~spl2_2 | ~spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f65,f61])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f16])).
% 1.29/0.53  fof(f16,conjecture,(
% 1.29/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 1.29/0.53  fof(f68,plain,(
% 1.29/0.53    spl2_2 | spl2_3),
% 1.29/0.53    inference(avatar_split_clause,[],[f32,f65,f61])).
% 1.29/0.53  fof(f32,plain,(
% 1.29/0.53    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f28])).
% 1.29/0.53  fof(f59,plain,(
% 1.29/0.53    spl2_1),
% 1.29/0.53    inference(avatar_split_clause,[],[f31,f56])).
% 1.29/0.53  fof(f31,plain,(
% 1.29/0.53    v1_relat_1(sK1)),
% 1.29/0.53    inference(cnf_transformation,[],[f28])).
% 1.29/0.53  % SZS output end Proof for theBenchmark
% 1.29/0.53  % (12595)------------------------------
% 1.29/0.53  % (12595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (12595)Termination reason: Refutation
% 1.29/0.53  
% 1.29/0.53  % (12595)Memory used [KB]: 10746
% 1.29/0.53  % (12595)Time elapsed: 0.057 s
% 1.29/0.53  % (12595)------------------------------
% 1.29/0.53  % (12595)------------------------------
% 1.29/0.53  % (12571)Success in time 0.162 s
%------------------------------------------------------------------------------
