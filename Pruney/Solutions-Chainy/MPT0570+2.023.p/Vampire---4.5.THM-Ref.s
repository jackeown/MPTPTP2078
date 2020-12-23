%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 115 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  185 ( 299 expanded)
%              Number of equality atoms :   52 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f139,f145,f163])).

fof(f163,plain,
    ( spl4_2
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl4_2
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f61,f144,f160])).

fof(f160,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f156,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f156,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,X4)
      | ~ r1_xboole_0(X4,X4) ) ),
    inference(forward_demodulation,[],[f152,f43])).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f152,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k4_xboole_0(X4,k1_xboole_0))
      | ~ r1_xboole_0(X4,X4) ) ),
    inference(superposition,[],[f48,f131])).

fof(f131,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f129,f109])).

fof(f109,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(superposition,[],[f50,f43])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f47,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f129,plain,(
    ! [X1] : k1_xboole_0 = k1_setfam_1(k2_tarski(X1,k1_xboole_0)) ),
    inference(global_subsumption,[],[f51,f123])).

fof(f123,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X1,k1_xboole_0))
      | ~ r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f109,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f144,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_11
  <=> r1_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f61,plain,
    ( k1_xboole_0 != sK0
    | spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f145,plain,
    ( spl4_11
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f140,f136,f64,f142])).

fof(f64,plain,
    ( spl4_3
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f136,plain,
    ( spl4_10
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f140,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(resolution,[],[f138,f79])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
        | r1_xboole_0(sK0,X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f36,f66])).

fof(f66,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f138,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( ~ spl4_1
    | spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f134,f69,f136,f54])).

fof(f54,plain,
    ( spl4_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f69,plain,
    ( spl4_4
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f134,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(superposition,[],[f34,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f72,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    & r1_tarski(sK0,k2_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).

fof(f20,plain,
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

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f67,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:33:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (2692)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (2700)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (2708)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (2697)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (2703)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (2703)Refutation not found, incomplete strategy% (2703)------------------------------
% 0.21/0.51  % (2703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2703)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2703)Memory used [KB]: 6268
% 0.21/0.51  % (2703)Time elapsed: 0.107 s
% 0.21/0.51  % (2716)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (2703)------------------------------
% 0.21/0.51  % (2703)------------------------------
% 0.21/0.52  % (2706)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (2716)Refutation not found, incomplete strategy% (2716)------------------------------
% 0.21/0.52  % (2716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2716)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2716)Memory used [KB]: 10746
% 0.21/0.52  % (2716)Time elapsed: 0.120 s
% 0.21/0.52  % (2716)------------------------------
% 0.21/0.52  % (2716)------------------------------
% 0.21/0.52  % (2706)Refutation not found, incomplete strategy% (2706)------------------------------
% 0.21/0.52  % (2706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2706)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2706)Memory used [KB]: 1663
% 0.21/0.52  % (2706)Time elapsed: 0.123 s
% 0.21/0.52  % (2706)------------------------------
% 0.21/0.52  % (2706)------------------------------
% 0.21/0.52  % (2715)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (2718)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (2698)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (2708)Refutation not found, incomplete strategy% (2708)------------------------------
% 0.21/0.52  % (2708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2708)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2708)Memory used [KB]: 10618
% 0.21/0.52  % (2708)Time elapsed: 0.116 s
% 0.21/0.52  % (2708)------------------------------
% 0.21/0.52  % (2708)------------------------------
% 0.21/0.52  % (2715)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f139,f145,f163])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl4_2 | ~spl4_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    $false | (spl4_2 | ~spl4_11)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f61,f144,f160])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(resolution,[],[f156,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(X5,X4) | ~r1_xboole_0(X4,X4)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f152,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(X5,k4_xboole_0(X4,k1_xboole_0)) | ~r1_xboole_0(X4,X4)) )),
% 0.21/0.52    inference(superposition,[],[f48,f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.21/0.52    inference(superposition,[],[f129,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,X0) = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.21/0.52    inference(superposition,[],[f50,f43])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f47,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X1,k1_xboole_0))) )),
% 0.21/0.52    inference(global_subsumption,[],[f51,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X1,k1_xboole_0)) | ~r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(superposition,[],[f109,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f46,f42])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    r1_xboole_0(sK0,sK0) | ~spl4_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f142])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    spl4_11 <=> r1_xboole_0(sK0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl4_2 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl4_11 | ~spl4_3 | ~spl4_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f140,f136,f64,f142])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    spl4_3 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    spl4_10 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    r1_xboole_0(sK0,sK0) | (~spl4_3 | ~spl4_10)),
% 0.21/0.52    inference(resolution,[],[f138,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(k2_relat_1(sK1),X0) | r1_xboole_0(sK0,X0)) ) | ~spl4_3),
% 0.21/0.52    inference(resolution,[],[f36,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f64])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f136])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ~spl4_1 | spl4_10 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f134,f69,f136,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl4_1 <=> v1_relat_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl4_4 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    r1_xboole_0(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.52    inference(superposition,[],[f34,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f69])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f69])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f64])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f59])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f54])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (2715)------------------------------
% 0.21/0.52  % (2715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2715)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (2715)Memory used [KB]: 10746
% 0.21/0.52  % (2715)Time elapsed: 0.081 s
% 0.21/0.52  % (2715)------------------------------
% 0.21/0.52  % (2715)------------------------------
% 0.21/0.52  % (2694)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (2704)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (2691)Success in time 0.164 s
%------------------------------------------------------------------------------
