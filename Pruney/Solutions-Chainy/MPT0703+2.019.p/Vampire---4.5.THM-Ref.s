%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 209 expanded)
%              Number of leaves         :   19 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  213 ( 510 expanded)
%              Number of equality atoms :   35 ( 100 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f405,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f180,f182,f184,f196,f217,f266,f276,f303,f335,f376,f387,f400])).

% (30165)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f400,plain,(
    ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | ~ spl3_24 ),
    inference(unit_resulting_resolution,[],[f23,f375,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f375,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl3_24
  <=> k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f23,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f387,plain,(
    spl3_23 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | spl3_23 ),
    inference(unit_resulting_resolution,[],[f22,f36,f371,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f371,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl3_23
  <=> r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f22,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f376,plain,
    ( ~ spl3_5
    | ~ spl3_23
    | ~ spl3_6
    | spl3_24
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f367,f300,f263,f373,f174,f369,f170])).

fof(f170,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f174,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f263,plain,
    ( spl3_13
  <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f300,plain,
    ( spl3_17
  <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f367,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f344,f302])).

fof(f302,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f300])).

fof(f344,plain,
    ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(superposition,[],[f27,f265])).

fof(f265,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f263])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f335,plain,(
    spl3_16 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f49,f298,f37])).

fof(f298,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl3_16
  <=> r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f44,f36])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f303,plain,
    ( ~ spl3_5
    | ~ spl3_16
    | ~ spl3_6
    | spl3_17
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f286,f273,f300,f174,f296,f170])).

fof(f273,plain,
    ( spl3_15
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f286,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_15 ),
    inference(superposition,[],[f27,f275])).

fof(f275,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f273])).

fof(f276,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_15
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f271,f193,f273,f174,f170])).

% (30158)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f193,plain,
    ( spl3_9
  <=> r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f271,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f258,f49])).

fof(f258,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(k1_xboole_0,sK1))
    | ~ spl3_9 ),
    inference(resolution,[],[f159,f195])).

fof(f195,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f193])).

fof(f159,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k10_relat_1(X3,X4),k10_relat_1(X3,X5))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k1_xboole_0 = k10_relat_1(X3,k6_subset_1(X4,X5)) ) ),
    inference(superposition,[],[f33,f38])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f266,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f256,f174,f170,f263])).

fof(f256,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f159,f21])).

fof(f21,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f217,plain,(
    ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f22,f191])).

fof(f191,plain,
    ( ! [X0] : ~ r1_tarski(sK0,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl3_8
  <=> ! [X0] : ~ r1_tarski(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f196,plain,
    ( spl3_8
    | spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f188,f178,f193,f190])).

fof(f178,plain,
    ( spl3_7
  <=> ! [X0] : r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f188,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1))
        | ~ r1_tarski(sK0,X0) )
    | ~ spl3_7 ),
    inference(superposition,[],[f179,f38])).

fof(f179,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f178])).

fof(f184,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f20,f176])).

fof(f176,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f174])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f182,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f19,f172])).

fof(f172,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f170])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f180,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f160,f178,f174,f170])).

fof(f160,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f130,f33])).

fof(f130,plain,(
    ! [X0] : r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),X0),k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f80,f36])).

fof(f80,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,k10_relat_1(sK2,sK0))
      | r1_tarski(X7,k10_relat_1(sK2,sK1)) ) ),
    inference(resolution,[],[f34,f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:31:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (30163)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (30171)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (30164)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (30170)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (30179)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (30169)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (30160)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (30173)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (30159)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (30171)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (30159)Refutation not found, incomplete strategy% (30159)------------------------------
% 0.21/0.53  % (30159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30159)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30159)Memory used [KB]: 1663
% 0.21/0.53  % (30159)Time elapsed: 0.102 s
% 0.21/0.53  % (30159)------------------------------
% 0.21/0.53  % (30159)------------------------------
% 0.21/0.53  % (30180)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (30162)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f405,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f180,f182,f184,f196,f217,f266,f276,f303,f335,f376,f387,f400])).
% 0.21/0.53  % (30165)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  fof(f400,plain,(
% 0.21/0.53    ~spl3_24),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f388])).
% 0.21/0.53  fof(f388,plain,(
% 0.21/0.53    $false | ~spl3_24),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f23,f375,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f32,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.53  fof(f375,plain,(
% 0.21/0.53    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~spl3_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f373])).
% 0.21/0.53  fof(f373,plain,(
% 0.21/0.53    spl3_24 <=> k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ~r1_tarski(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 0.21/0.53  fof(f387,plain,(
% 0.21/0.53    spl3_23),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f380])).
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    $false | spl3_23),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f22,f36,f371,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | spl3_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f369])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    spl3_23 <=> r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f26])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    ~spl3_5 | ~spl3_23 | ~spl3_6 | spl3_24 | ~spl3_13 | ~spl3_17),
% 0.21/0.53    inference(avatar_split_clause,[],[f367,f300,f263,f373,f174,f369,f170])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    spl3_5 <=> v1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    spl3_6 <=> v1_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    spl3_13 <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    spl3_17 <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.53  fof(f367,plain,(
% 0.21/0.53    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~v1_funct_1(sK2) | ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_13 | ~spl3_17)),
% 0.21/0.53    inference(forward_demodulation,[],[f344,f302])).
% 0.21/0.53  fof(f302,plain,(
% 0.21/0.53    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~spl3_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f300])).
% 0.21/0.53  fof(f344,plain,(
% 0.21/0.53    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | ~v1_funct_1(sK2) | ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_13),
% 0.21/0.53    inference(superposition,[],[f27,f265])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~spl3_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f263])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.53  fof(f335,plain,(
% 0.21/0.53    spl3_16),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f317])).
% 0.21/0.53  fof(f317,plain,(
% 0.21/0.53    $false | spl3_16),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f49,f298,f37])).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | spl3_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f296])).
% 0.21/0.53  fof(f296,plain,(
% 0.21/0.53    spl3_16 <=> r1_tarski(k1_xboole_0,k2_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f44,f36])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(superposition,[],[f38,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f24,f26])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f31,f26])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f303,plain,(
% 0.21/0.54    ~spl3_5 | ~spl3_16 | ~spl3_6 | spl3_17 | ~spl3_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f286,f273,f300,f174,f296,f170])).
% 0.21/0.54  fof(f273,plain,(
% 0.21/0.54    spl3_15 <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~v1_funct_1(sK2) | ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_15),
% 0.21/0.54    inference(superposition,[],[f27,f275])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~spl3_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f273])).
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    ~spl3_5 | ~spl3_6 | spl3_15 | ~spl3_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f271,f193,f273,f174,f170])).
% 0.21/0.54  % (30158)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  fof(f193,plain,(
% 0.21/0.54    spl3_9 <=> r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_9),
% 0.21/0.54    inference(forward_demodulation,[],[f258,f49])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(k1_xboole_0,sK1)) | ~spl3_9),
% 0.21/0.54    inference(resolution,[],[f159,f195])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1)) | ~spl3_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f193])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~r1_tarski(k10_relat_1(X3,X4),k10_relat_1(X3,X5)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k1_xboole_0 = k10_relat_1(X3,k6_subset_1(X4,X5))) )),
% 0.21/0.54    inference(superposition,[],[f33,f38])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    spl3_13 | ~spl3_5 | ~spl3_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f256,f174,f170,f263])).
% 0.21/0.54  fof(f256,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.21/0.54    inference(resolution,[],[f159,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    ~spl3_8),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f204])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    $false | ~spl3_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f22,f191])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(sK0,X0)) ) | ~spl3_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f190])).
% 0.21/0.54  fof(f190,plain,(
% 0.21/0.54    spl3_8 <=> ! [X0] : ~r1_tarski(sK0,X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.54  fof(f196,plain,(
% 0.21/0.54    spl3_8 | spl3_9 | ~spl3_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f188,f178,f193,f190])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    spl3_7 <=> ! [X0] : r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.54  fof(f188,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k1_xboole_0),k10_relat_1(sK2,sK1)) | ~r1_tarski(sK0,X0)) ) | ~spl3_7),
% 0.21/0.54    inference(superposition,[],[f179,f38])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1))) ) | ~spl3_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f178])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    spl3_6),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f183])).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    $false | spl3_6),
% 0.21/0.54    inference(subsumption_resolution,[],[f20,f176])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | spl3_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f174])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    spl3_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    $false | spl3_5),
% 0.21/0.54    inference(subsumption_resolution,[],[f19,f172])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | spl3_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f170])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    v1_relat_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    ~spl3_5 | ~spl3_6 | spl3_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f160,f178,f174,f170])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,X0)),k10_relat_1(sK2,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.54    inference(superposition,[],[f130,f33])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),X0),k10_relat_1(sK2,sK1))) )),
% 0.21/0.54    inference(resolution,[],[f80,f36])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X7] : (~r1_tarski(X7,k10_relat_1(sK2,sK0)) | r1_tarski(X7,k10_relat_1(sK2,sK1))) )),
% 0.21/0.54    inference(resolution,[],[f34,f21])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (30171)------------------------------
% 0.21/0.54  % (30171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30171)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (30171)Memory used [KB]: 6396
% 0.21/0.54  % (30171)Time elapsed: 0.119 s
% 0.21/0.54  % (30171)------------------------------
% 0.21/0.54  % (30171)------------------------------
% 0.21/0.54  % (30157)Success in time 0.172 s
%------------------------------------------------------------------------------
