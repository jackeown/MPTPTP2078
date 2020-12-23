%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 188 expanded)
%              Number of leaves         :   20 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  221 ( 509 expanded)
%              Number of equality atoms :   42 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f701,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f142,f190,f209,f402,f439,f700])).

fof(f700,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_8
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f699])).

fof(f699,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_8
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f698,f141])).

fof(f141,plain,
    ( k1_xboole_0 != k6_subset_1(sK0,sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_8
  <=> k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f698,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f695,f438])).

fof(f438,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl3_19
  <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f695,plain,
    ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(superposition,[],[f161,f401])).

fof(f401,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl3_18
  <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f161,plain,
    ( ! [X0] : k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f43,f48,f87,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f87,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f37,f58,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f58,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_4
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f48,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f43,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f439,plain,
    ( spl3_19
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f430,f187,f46,f41,f436])).

fof(f187,plain,
    ( spl3_11
  <=> k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f430,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f189,f429])).

fof(f429,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f411,f134])).

fof(f134,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f30])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f65,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f37,f36])).

fof(f36,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f411,plain,
    ( ! [X1] : k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X1,X1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f134,f103])).

fof(f103,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f43,f48,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f189,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f187])).

fof(f402,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f355,f206,f46,f41,f399])).

fof(f206,plain,
    ( spl3_14
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f355,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(superposition,[],[f103,f208])).

fof(f208,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f206])).

fof(f209,plain,
    ( spl3_14
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f68,f61,f206])).

fof(f61,plain,
    ( spl3_5
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f63,f38])).

fof(f63,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f190,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f98,f46,f41,f187])).

fof(f98,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f43,f48,f27,f31])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f142,plain,
    ( ~ spl3_8
    | spl3_3 ),
    inference(avatar_split_clause,[],[f74,f51,f139])).

fof(f51,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f74,plain,
    ( k1_xboole_0 != k6_subset_1(sK0,sK1)
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f53,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f64,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f61])).

fof(f24,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f59,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:47:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (9795)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (9792)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (9790)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (9791)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (9795)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f701,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f142,f190,f209,f402,f439,f700])).
% 0.21/0.48  fof(f700,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_8 | ~spl3_18 | ~spl3_19),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f699])).
% 0.21/0.48  fof(f699,plain,(
% 0.21/0.48    $false | (~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_8 | ~spl3_18 | ~spl3_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f698,f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    k1_xboole_0 != k6_subset_1(sK0,sK1) | spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f139])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl3_8 <=> k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f698,plain,(
% 0.21/0.48    k1_xboole_0 = k6_subset_1(sK0,sK1) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_18 | ~spl3_19)),
% 0.21/0.48    inference(forward_demodulation,[],[f695,f438])).
% 0.21/0.48  fof(f438,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~spl3_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f436])).
% 0.21/0.48  fof(f436,plain,(
% 0.21/0.48    spl3_19 <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.48  fof(f695,plain,(
% 0.21/0.48    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_18)),
% 0.21/0.48    inference(superposition,[],[f161,f401])).
% 0.21/0.48  fof(f401,plain,(
% 0.21/0.48    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~spl3_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f399])).
% 0.21/0.48  fof(f399,plain,(
% 0.21/0.48    spl3_18 <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ( ! [X0] : (k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f43,f48,f87,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))) ) | ~spl3_4),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f37,f58,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl3_4 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f29,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl3_2 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f439,plain,(
% 0.21/0.48    spl3_19 | ~spl3_1 | ~spl3_2 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f430,f187,f46,f41,f436])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    spl3_11 <=> k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f430,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | (~spl3_1 | ~spl3_2 | ~spl3_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f189,f429])).
% 0.21/0.48  fof(f429,plain,(
% 0.21/0.48    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(forward_demodulation,[],[f411,f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f65,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f33,f30])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.48    inference(superposition,[],[f37,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f28,f30])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.48  fof(f411,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X1,X1))) ) | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(superposition,[],[f134,f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f43,f48,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f187])).
% 0.21/0.48  fof(f402,plain,(
% 0.21/0.48    spl3_18 | ~spl3_1 | ~spl3_2 | ~spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f355,f206,f46,f41,f399])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    spl3_14 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f355,plain,(
% 0.21/0.48    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_14)),
% 0.21/0.48    inference(superposition,[],[f103,f208])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f206])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    spl3_14 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f68,f61,f206])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl3_5 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_5),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f63,f38])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    spl3_11 | ~spl3_1 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f46,f41,f187])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f43,f48,f27,f31])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ~spl3_8 | spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f74,f51,f139])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    k1_xboole_0 != k6_subset_1(sK0,sK1) | spl3_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f53,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f32,f30])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f61])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f56])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f51])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f46])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f41])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9795)------------------------------
% 0.21/0.48  % (9795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9795)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9795)Memory used [KB]: 11001
% 0.21/0.48  % (9795)Time elapsed: 0.016 s
% 0.21/0.48  % (9795)------------------------------
% 0.21/0.48  % (9795)------------------------------
% 0.21/0.48  % (9784)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (9777)Success in time 0.12 s
%------------------------------------------------------------------------------
