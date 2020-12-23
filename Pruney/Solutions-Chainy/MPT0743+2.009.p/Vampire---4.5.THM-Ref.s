%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 422 expanded)
%              Number of leaves         :   33 ( 182 expanded)
%              Depth                    :   10
%              Number of atoms          :  492 (1161 expanded)
%              Number of equality atoms :   24 (  47 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f700,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f83,f90,f127,f162,f164,f197,f204,f226,f230,f231,f236,f319,f331,f339,f384,f409,f413,f430,f483,f504,f516,f575,f594,f596,f600,f653,f699])).

fof(f699,plain,
    ( spl2_18
    | ~ spl2_43 ),
    inference(avatar_contradiction_clause,[],[f698])).

fof(f698,plain,
    ( $false
    | spl2_18
    | ~ spl2_43 ),
    inference(subsumption_resolution,[],[f693,f225])).

fof(f225,plain,
    ( ~ r2_hidden(sK0,sK0)
    | spl2_18 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl2_18
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f693,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl2_43 ),
    inference(superposition,[],[f58,f495])).

fof(f495,plain,
    ( sK0 = k1_ordinal1(sK0)
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl2_43
  <=> sK0 = k1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f58,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f653,plain,
    ( spl2_43
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_19
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f599,f382,f228,f88,f66,f494])).

fof(f66,plain,
    ( spl2_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f88,plain,
    ( spl2_6
  <=> v3_ordinal1(k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f228,plain,
    ( spl2_19
  <=> r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f382,plain,
    ( spl2_39
  <=> r1_tarski(sK0,k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f599,plain,
    ( sK0 = k1_ordinal1(sK0)
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_19
    | ~ spl2_39 ),
    inference(subsumption_resolution,[],[f405,f598])).

fof(f598,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK0)
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f597,f89])).

fof(f89,plain,
    ( v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f597,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl2_2
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f459,f67])).

fof(f67,plain,
    ( v3_ordinal1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f459,plain,
    ( ~ v3_ordinal1(sK0)
    | r1_tarski(k1_ordinal1(sK0),sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl2_19 ),
    inference(resolution,[],[f229,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f229,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f228])).

fof(f405,plain,
    ( ~ r1_tarski(k1_ordinal1(sK0),sK0)
    | sK0 = k1_ordinal1(sK0)
    | ~ spl2_39 ),
    inference(resolution,[],[f383,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f383,plain,
    ( r1_tarski(sK0,k1_ordinal1(sK0))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f382])).

fof(f600,plain,
    ( sK1 != k1_ordinal1(sK0)
    | r2_hidden(k1_ordinal1(sK0),sK0)
    | ~ r2_hidden(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f596,plain,
    ( ~ spl2_14
    | ~ spl2_31 ),
    inference(avatar_contradiction_clause,[],[f595])).

% (16474)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f595,plain,
    ( $false
    | ~ spl2_14
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f509,f322])).

fof(f322,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ spl2_31 ),
    inference(resolution,[],[f315,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f315,plain,
    ( r2_hidden(k1_ordinal1(sK0),sK1)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl2_31
  <=> r2_hidden(k1_ordinal1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f509,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ spl2_14 ),
    inference(resolution,[],[f215,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f215,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl2_14
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f594,plain,
    ( ~ spl2_7
    | ~ spl2_13
    | ~ spl2_31
    | spl2_33
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl2_7
    | ~ spl2_13
    | ~ spl2_31
    | spl2_33
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(subsumption_resolution,[],[f592,f485])).

fof(f485,plain,
    ( ~ r2_hidden(k1_ordinal1(sK0),sK0)
    | spl2_33 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl2_33
  <=> r2_hidden(k1_ordinal1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f592,plain,
    ( r2_hidden(k1_ordinal1(sK0),sK0)
    | ~ spl2_7
    | ~ spl2_13
    | ~ spl2_31
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(forward_demodulation,[],[f315,f585])).

fof(f585,plain,
    ( sK0 = sK1
    | ~ spl2_7
    | ~ spl2_13
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(subsumption_resolution,[],[f519,f584])).

fof(f584,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_7
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(forward_demodulation,[],[f100,f502])).

fof(f502,plain,
    ( sK0 = k1_ordinal1(sK0)
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(subsumption_resolution,[],[f405,f482])).

fof(f482,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK0)
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f481])).

fof(f481,plain,
    ( spl2_41
  <=> r1_tarski(k1_ordinal1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f100,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_7
  <=> r1_tarski(k1_ordinal1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f519,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | ~ spl2_13 ),
    inference(resolution,[],[f145,f54])).

fof(f145,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl2_13
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f575,plain,
    ( spl2_51
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f501,f411,f88,f81,f62,f573])).

fof(f573,plain,
    ( spl2_51
  <=> sK1 = k1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f62,plain,
    ( spl2_1
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f81,plain,
    ( spl2_5
  <=> r1_ordinal1(k1_ordinal1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f411,plain,
    ( spl2_40
  <=> r1_tarski(sK1,k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f501,plain,
    ( sK1 = k1_ordinal1(sK0)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_40 ),
    inference(subsumption_resolution,[],[f424,f93])).

fof(f93,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f92,f89])).

fof(f92,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f91,f63])).

fof(f63,plain,
    ( v3_ordinal1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f91,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl2_5 ),
    inference(resolution,[],[f82,f36])).

fof(f82,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f424,plain,
    ( ~ r1_tarski(k1_ordinal1(sK0),sK1)
    | sK1 = k1_ordinal1(sK0)
    | ~ spl2_40 ),
    inference(resolution,[],[f412,f54])).

fof(f412,plain,
    ( r1_tarski(sK1,k1_ordinal1(sK0))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f411])).

fof(f516,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f136,f125,f66,f62,f144])).

fof(f125,plain,
    ( spl2_10
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f136,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f135,f63])).

fof(f135,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f134,f67])).

fof(f134,plain,
    ( ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl2_10 ),
    inference(resolution,[],[f126,f36])).

fof(f126,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f504,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f93,f88,f81,f62,f99])).

fof(f483,plain,
    ( spl2_41
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f440,f202,f99,f481])).

fof(f202,plain,
    ( spl2_17
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f440,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK0)
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f100,f203])).

fof(f203,plain,
    ( sK0 = sK1
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f202])).

fof(f430,plain,
    ( spl2_17
    | spl2_14
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f419,f371,f160,f202])).

fof(f371,plain,
    ( spl2_38
  <=> r2_hidden(sK1,k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f419,plain,
    ( sK0 = sK1
    | spl2_14
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f414,f161])).

fof(f161,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f414,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ spl2_38 ),
    inference(resolution,[],[f408,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | X0 = X1
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f408,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f371])).

fof(f413,plain,
    ( spl2_40
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f397,f317,f88,f62,f411])).

fof(f317,plain,
    ( spl2_32
  <=> r1_ordinal1(sK1,k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f397,plain,
    ( r1_tarski(sK1,k1_ordinal1(sK0))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f396,f63])).

fof(f396,plain,
    ( r1_tarski(sK1,k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK1)
    | ~ spl2_6
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f395,f89])).

fof(f395,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | r1_tarski(sK1,k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK1)
    | ~ spl2_32 ),
    inference(resolution,[],[f318,f36])).

fof(f318,plain,
    ( r1_ordinal1(sK1,k1_ordinal1(sK0))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f317])).

fof(f409,plain,
    ( spl2_38
    | ~ spl2_1
    | spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f391,f88,f81,f62,f371])).

fof(f391,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ spl2_1
    | spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f385,f163])).

fof(f163,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f385,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(resolution,[],[f97,f63])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_ordinal1(k1_ordinal1(sK0),X0)
        | r2_hidden(X0,k1_ordinal1(sK0)) )
    | ~ spl2_6 ),
    inference(resolution,[],[f89,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f384,plain,
    ( spl2_39
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f342,f329,f88,f66,f382])).

fof(f329,plain,
    ( spl2_34
  <=> r1_ordinal1(sK0,k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f342,plain,
    ( r1_tarski(sK0,k1_ordinal1(sK0))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f341,f67])).

fof(f341,plain,
    ( r1_tarski(sK0,k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK0)
    | ~ spl2_6
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f340,f89])).

fof(f340,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | r1_tarski(sK0,k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK0)
    | ~ spl2_34 ),
    inference(resolution,[],[f330,f36])).

fof(f330,plain,
    ( r1_ordinal1(sK0,k1_ordinal1(sK0))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f329])).

fof(f339,plain,(
    ~ spl2_33 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f335,f46])).

fof(f335,plain,
    ( r2_hidden(k1_ordinal1(sK0),k1_ordinal1(sK0))
    | ~ spl2_33 ),
    inference(resolution,[],[f327,f39])).

fof(f327,plain,
    ( r2_hidden(k1_ordinal1(sK0),sK0)
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f326])).

fof(f331,plain,
    ( spl2_33
    | spl2_34
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f122,f88,f66,f329,f326])).

fof(f122,plain,
    ( r1_ordinal1(sK0,k1_ordinal1(sK0))
    | r2_hidden(k1_ordinal1(sK0),sK0)
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f72,f89])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_ordinal1(sK0,X0)
        | r2_hidden(X0,sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f67,f37])).

fof(f319,plain,
    ( spl2_31
    | spl2_32
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f112,f88,f62,f317,f314])).

fof(f112,plain,
    ( r1_ordinal1(sK1,k1_ordinal1(sK0))
    | r2_hidden(k1_ordinal1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(resolution,[],[f70,f89])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_ordinal1(sK1,X0)
        | r2_hidden(X0,sK1) )
    | ~ spl2_1 ),
    inference(resolution,[],[f63,f37])).

fof(f236,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_2
    | spl2_14 ),
    inference(avatar_split_clause,[],[f169,f160,f66,f62,f166])).

fof(f166,plain,
    ( spl2_15
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f169,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | spl2_14 ),
    inference(subsumption_resolution,[],[f119,f161])).

fof(f119,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f72,f63])).

fof(f231,plain,
    ( sK0 != sK1
    | r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f230,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f200,f166,f144,f81,f66,f62,f228])).

fof(f200,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f82,f186])).

fof(f186,plain,
    ( sK0 = sK1
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f183,f178])).

fof(f178,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f177,f67])).

fof(f177,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f176,f63])).

fof(f176,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl2_15 ),
    inference(resolution,[],[f167,f36])).

fof(f167,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f183,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | ~ spl2_13 ),
    inference(resolution,[],[f145,f54])).

fof(f226,plain,
    ( ~ spl2_18
    | ~ spl2_13
    | spl2_14
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f222,f195,f160,f144,f224])).

fof(f195,plain,
    ( spl2_16
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f222,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ spl2_13
    | spl2_14
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f161,f205])).

fof(f205,plain,
    ( sK0 = sK1
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f183,f196])).

fof(f196,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f195])).

fof(f204,plain,
    ( spl2_17
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f186,f166,f144,f66,f62,f202])).

fof(f197,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f178,f166,f66,f62,f195])).

fof(f164,plain,
    ( ~ spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f153,f78,f81])).

fof(f78,plain,
    ( spl2_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f153,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f32,f79])).

fof(f79,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f32,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f162,plain,
    ( ~ spl2_14
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f155,f78,f160])).

fof(f155,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f79,f46])).

fof(f127,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f114,f78,f66,f62,f125])).

fof(f114,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(subsumption_resolution,[],[f110,f85])).

fof(f85,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f110,plain,
    ( r1_ordinal1(sK1,sK0)
    | r2_hidden(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f70,f67])).

fof(f90,plain,
    ( spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f71,f66,f88])).

fof(f71,plain,
    ( v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f67,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f83,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f31,f81,f78])).

fof(f31,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f34,f66])).

fof(f34,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:51:06 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.49  % (16470)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (16485)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (16494)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (16482)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (16482)Refutation not found, incomplete strategy% (16482)------------------------------
% 0.20/0.53  % (16482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16480)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (16482)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16482)Memory used [KB]: 10618
% 0.20/0.53  % (16482)Time elapsed: 0.066 s
% 0.20/0.53  % (16482)------------------------------
% 0.20/0.53  % (16482)------------------------------
% 0.20/0.53  % (16486)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (16492)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (16465)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (16491)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (16471)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (16489)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (16466)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (16496)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (16496)Refutation not found, incomplete strategy% (16496)------------------------------
% 0.20/0.54  % (16496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16496)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16496)Memory used [KB]: 10746
% 0.20/0.54  % (16496)Time elapsed: 0.125 s
% 0.20/0.54  % (16496)------------------------------
% 0.20/0.54  % (16496)------------------------------
% 0.20/0.55  % (16467)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.55  % (16469)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.55  % (16477)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (16490)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (16495)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (16494)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f700,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f64,f68,f83,f90,f127,f162,f164,f197,f204,f226,f230,f231,f236,f319,f331,f339,f384,f409,f413,f430,f483,f504,f516,f575,f594,f596,f600,f653,f699])).
% 0.20/0.55  fof(f699,plain,(
% 0.20/0.55    spl2_18 | ~spl2_43),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f698])).
% 0.20/0.55  fof(f698,plain,(
% 0.20/0.55    $false | (spl2_18 | ~spl2_43)),
% 0.20/0.55    inference(subsumption_resolution,[],[f693,f225])).
% 0.20/0.55  fof(f225,plain,(
% 0.20/0.55    ~r2_hidden(sK0,sK0) | spl2_18),
% 0.20/0.55    inference(avatar_component_clause,[],[f224])).
% 0.20/0.55  fof(f224,plain,(
% 0.20/0.55    spl2_18 <=> r2_hidden(sK0,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.55  fof(f693,plain,(
% 0.20/0.55    r2_hidden(sK0,sK0) | ~spl2_43),
% 0.20/0.55    inference(superposition,[],[f58,f495])).
% 0.20/0.55  fof(f495,plain,(
% 0.20/0.55    sK0 = k1_ordinal1(sK0) | ~spl2_43),
% 0.20/0.55    inference(avatar_component_clause,[],[f494])).
% 0.20/0.55  fof(f494,plain,(
% 0.20/0.55    spl2_43 <=> sK0 = k1_ordinal1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.20/0.55    inference(equality_resolution,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X0,X1] : (X0 != X1 | r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,axiom,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.20/0.55  fof(f653,plain,(
% 0.20/0.55    spl2_43 | ~spl2_2 | ~spl2_6 | ~spl2_19 | ~spl2_39),
% 0.20/0.55    inference(avatar_split_clause,[],[f599,f382,f228,f88,f66,f494])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    spl2_2 <=> v3_ordinal1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    spl2_6 <=> v3_ordinal1(k1_ordinal1(sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.55  fof(f228,plain,(
% 0.20/0.55    spl2_19 <=> r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.55  fof(f382,plain,(
% 0.20/0.55    spl2_39 <=> r1_tarski(sK0,k1_ordinal1(sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.20/0.55  fof(f599,plain,(
% 0.20/0.55    sK0 = k1_ordinal1(sK0) | (~spl2_2 | ~spl2_6 | ~spl2_19 | ~spl2_39)),
% 0.20/0.55    inference(subsumption_resolution,[],[f405,f598])).
% 0.20/0.55  fof(f598,plain,(
% 0.20/0.55    r1_tarski(k1_ordinal1(sK0),sK0) | (~spl2_2 | ~spl2_6 | ~spl2_19)),
% 0.20/0.55    inference(subsumption_resolution,[],[f597,f89])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    v3_ordinal1(k1_ordinal1(sK0)) | ~spl2_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f88])).
% 0.20/0.55  fof(f597,plain,(
% 0.20/0.55    r1_tarski(k1_ordinal1(sK0),sK0) | ~v3_ordinal1(k1_ordinal1(sK0)) | (~spl2_2 | ~spl2_19)),
% 0.20/0.55    inference(subsumption_resolution,[],[f459,f67])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    v3_ordinal1(sK0) | ~spl2_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f66])).
% 0.20/0.55  fof(f459,plain,(
% 0.20/0.55    ~v3_ordinal1(sK0) | r1_tarski(k1_ordinal1(sK0),sK0) | ~v3_ordinal1(k1_ordinal1(sK0)) | ~spl2_19),
% 0.20/0.55    inference(resolution,[],[f229,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.55  fof(f229,plain,(
% 0.20/0.55    r1_ordinal1(k1_ordinal1(sK0),sK0) | ~spl2_19),
% 0.20/0.55    inference(avatar_component_clause,[],[f228])).
% 0.20/0.55  fof(f405,plain,(
% 0.20/0.55    ~r1_tarski(k1_ordinal1(sK0),sK0) | sK0 = k1_ordinal1(sK0) | ~spl2_39),
% 0.20/0.55    inference(resolution,[],[f383,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f383,plain,(
% 0.20/0.55    r1_tarski(sK0,k1_ordinal1(sK0)) | ~spl2_39),
% 0.20/0.55    inference(avatar_component_clause,[],[f382])).
% 0.20/0.55  fof(f600,plain,(
% 0.20/0.55    sK1 != k1_ordinal1(sK0) | r2_hidden(k1_ordinal1(sK0),sK0) | ~r2_hidden(sK1,sK0)),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f596,plain,(
% 0.20/0.55    ~spl2_14 | ~spl2_31),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f595])).
% 0.20/0.55  % (16474)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  fof(f595,plain,(
% 0.20/0.55    $false | (~spl2_14 | ~spl2_31)),
% 0.20/0.55    inference(subsumption_resolution,[],[f509,f322])).
% 0.20/0.55  fof(f322,plain,(
% 0.20/0.55    ~r2_hidden(sK1,k1_ordinal1(sK0)) | ~spl2_31),
% 0.20/0.55    inference(resolution,[],[f315,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.55  fof(f315,plain,(
% 0.20/0.55    r2_hidden(k1_ordinal1(sK0),sK1) | ~spl2_31),
% 0.20/0.55    inference(avatar_component_clause,[],[f314])).
% 0.20/0.55  fof(f314,plain,(
% 0.20/0.55    spl2_31 <=> r2_hidden(k1_ordinal1(sK0),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.20/0.55  fof(f509,plain,(
% 0.20/0.55    r2_hidden(sK1,k1_ordinal1(sK0)) | ~spl2_14),
% 0.20/0.55    inference(resolution,[],[f215,f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f215,plain,(
% 0.20/0.55    r2_hidden(sK1,sK0) | ~spl2_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f160])).
% 0.20/0.55  fof(f160,plain,(
% 0.20/0.55    spl2_14 <=> r2_hidden(sK1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.55  fof(f594,plain,(
% 0.20/0.55    ~spl2_7 | ~spl2_13 | ~spl2_31 | spl2_33 | ~spl2_39 | ~spl2_41),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f593])).
% 0.20/0.55  fof(f593,plain,(
% 0.20/0.55    $false | (~spl2_7 | ~spl2_13 | ~spl2_31 | spl2_33 | ~spl2_39 | ~spl2_41)),
% 0.20/0.55    inference(subsumption_resolution,[],[f592,f485])).
% 0.20/0.55  fof(f485,plain,(
% 0.20/0.55    ~r2_hidden(k1_ordinal1(sK0),sK0) | spl2_33),
% 0.20/0.55    inference(avatar_component_clause,[],[f326])).
% 0.20/0.55  fof(f326,plain,(
% 0.20/0.55    spl2_33 <=> r2_hidden(k1_ordinal1(sK0),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.20/0.55  fof(f592,plain,(
% 0.20/0.55    r2_hidden(k1_ordinal1(sK0),sK0) | (~spl2_7 | ~spl2_13 | ~spl2_31 | ~spl2_39 | ~spl2_41)),
% 0.20/0.55    inference(forward_demodulation,[],[f315,f585])).
% 0.20/0.55  fof(f585,plain,(
% 0.20/0.55    sK0 = sK1 | (~spl2_7 | ~spl2_13 | ~spl2_39 | ~spl2_41)),
% 0.20/0.55    inference(subsumption_resolution,[],[f519,f584])).
% 0.20/0.55  fof(f584,plain,(
% 0.20/0.55    r1_tarski(sK0,sK1) | (~spl2_7 | ~spl2_39 | ~spl2_41)),
% 0.20/0.55    inference(forward_demodulation,[],[f100,f502])).
% 0.20/0.55  fof(f502,plain,(
% 0.20/0.55    sK0 = k1_ordinal1(sK0) | (~spl2_39 | ~spl2_41)),
% 0.20/0.55    inference(subsumption_resolution,[],[f405,f482])).
% 0.20/0.55  fof(f482,plain,(
% 0.20/0.55    r1_tarski(k1_ordinal1(sK0),sK0) | ~spl2_41),
% 0.20/0.55    inference(avatar_component_clause,[],[f481])).
% 0.20/0.55  fof(f481,plain,(
% 0.20/0.55    spl2_41 <=> r1_tarski(k1_ordinal1(sK0),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    r1_tarski(k1_ordinal1(sK0),sK1) | ~spl2_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f99])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    spl2_7 <=> r1_tarski(k1_ordinal1(sK0),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.55  fof(f519,plain,(
% 0.20/0.55    ~r1_tarski(sK0,sK1) | sK0 = sK1 | ~spl2_13),
% 0.20/0.55    inference(resolution,[],[f145,f54])).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    r1_tarski(sK1,sK0) | ~spl2_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f144])).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    spl2_13 <=> r1_tarski(sK1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.55  fof(f575,plain,(
% 0.20/0.55    spl2_51 | ~spl2_1 | ~spl2_5 | ~spl2_6 | ~spl2_40),
% 0.20/0.55    inference(avatar_split_clause,[],[f501,f411,f88,f81,f62,f573])).
% 0.20/0.55  fof(f573,plain,(
% 0.20/0.55    spl2_51 <=> sK1 = k1_ordinal1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    spl2_1 <=> v3_ordinal1(sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    spl2_5 <=> r1_ordinal1(k1_ordinal1(sK0),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.55  fof(f411,plain,(
% 0.20/0.55    spl2_40 <=> r1_tarski(sK1,k1_ordinal1(sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.20/0.55  fof(f501,plain,(
% 0.20/0.55    sK1 = k1_ordinal1(sK0) | (~spl2_1 | ~spl2_5 | ~spl2_6 | ~spl2_40)),
% 0.20/0.55    inference(subsumption_resolution,[],[f424,f93])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    r1_tarski(k1_ordinal1(sK0),sK1) | (~spl2_1 | ~spl2_5 | ~spl2_6)),
% 0.20/0.55    inference(subsumption_resolution,[],[f92,f89])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | (~spl2_1 | ~spl2_5)),
% 0.20/0.55    inference(subsumption_resolution,[],[f91,f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    v3_ordinal1(sK1) | ~spl2_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f62])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    ~v3_ordinal1(sK1) | r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | ~spl2_5),
% 0.20/0.55    inference(resolution,[],[f82,f36])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    r1_ordinal1(k1_ordinal1(sK0),sK1) | ~spl2_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f81])).
% 0.20/0.55  fof(f424,plain,(
% 0.20/0.55    ~r1_tarski(k1_ordinal1(sK0),sK1) | sK1 = k1_ordinal1(sK0) | ~spl2_40),
% 0.20/0.55    inference(resolution,[],[f412,f54])).
% 0.20/0.55  fof(f412,plain,(
% 0.20/0.55    r1_tarski(sK1,k1_ordinal1(sK0)) | ~spl2_40),
% 0.20/0.55    inference(avatar_component_clause,[],[f411])).
% 0.20/0.55  fof(f516,plain,(
% 0.20/0.55    spl2_13 | ~spl2_1 | ~spl2_2 | ~spl2_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f136,f125,f66,f62,f144])).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    spl2_10 <=> r1_ordinal1(sK1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    r1_tarski(sK1,sK0) | (~spl2_1 | ~spl2_2 | ~spl2_10)),
% 0.20/0.55    inference(subsumption_resolution,[],[f135,f63])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1) | (~spl2_2 | ~spl2_10)),
% 0.20/0.55    inference(subsumption_resolution,[],[f134,f67])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    ~v3_ordinal1(sK0) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1) | ~spl2_10),
% 0.20/0.55    inference(resolution,[],[f126,f36])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    r1_ordinal1(sK1,sK0) | ~spl2_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f125])).
% 0.20/0.55  fof(f504,plain,(
% 0.20/0.55    spl2_7 | ~spl2_1 | ~spl2_5 | ~spl2_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f93,f88,f81,f62,f99])).
% 0.20/0.55  fof(f483,plain,(
% 0.20/0.55    spl2_41 | ~spl2_7 | ~spl2_17),
% 0.20/0.55    inference(avatar_split_clause,[],[f440,f202,f99,f481])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    spl2_17 <=> sK0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.55  fof(f440,plain,(
% 0.20/0.55    r1_tarski(k1_ordinal1(sK0),sK0) | (~spl2_7 | ~spl2_17)),
% 0.20/0.55    inference(forward_demodulation,[],[f100,f203])).
% 0.20/0.55  fof(f203,plain,(
% 0.20/0.55    sK0 = sK1 | ~spl2_17),
% 0.20/0.55    inference(avatar_component_clause,[],[f202])).
% 0.20/0.55  fof(f430,plain,(
% 0.20/0.55    spl2_17 | spl2_14 | ~spl2_38),
% 0.20/0.55    inference(avatar_split_clause,[],[f419,f371,f160,f202])).
% 0.20/0.55  fof(f371,plain,(
% 0.20/0.55    spl2_38 <=> r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.20/0.55  fof(f419,plain,(
% 0.20/0.55    sK0 = sK1 | (spl2_14 | ~spl2_38)),
% 0.20/0.55    inference(subsumption_resolution,[],[f414,f161])).
% 0.20/0.55  fof(f161,plain,(
% 0.20/0.55    ~r2_hidden(sK1,sK0) | spl2_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f160])).
% 0.20/0.55  fof(f414,plain,(
% 0.20/0.55    sK0 = sK1 | r2_hidden(sK1,sK0) | ~spl2_38),
% 0.20/0.55    inference(resolution,[],[f408,f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | X0 = X1 | r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f408,plain,(
% 0.20/0.55    r2_hidden(sK1,k1_ordinal1(sK0)) | ~spl2_38),
% 0.20/0.55    inference(avatar_component_clause,[],[f371])).
% 0.20/0.55  fof(f413,plain,(
% 0.20/0.55    spl2_40 | ~spl2_1 | ~spl2_6 | ~spl2_32),
% 0.20/0.55    inference(avatar_split_clause,[],[f397,f317,f88,f62,f411])).
% 0.20/0.55  fof(f317,plain,(
% 0.20/0.55    spl2_32 <=> r1_ordinal1(sK1,k1_ordinal1(sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.20/0.55  fof(f397,plain,(
% 0.20/0.55    r1_tarski(sK1,k1_ordinal1(sK0)) | (~spl2_1 | ~spl2_6 | ~spl2_32)),
% 0.20/0.55    inference(subsumption_resolution,[],[f396,f63])).
% 0.20/0.55  fof(f396,plain,(
% 0.20/0.55    r1_tarski(sK1,k1_ordinal1(sK0)) | ~v3_ordinal1(sK1) | (~spl2_6 | ~spl2_32)),
% 0.20/0.55    inference(subsumption_resolution,[],[f395,f89])).
% 0.20/0.55  fof(f395,plain,(
% 0.20/0.55    ~v3_ordinal1(k1_ordinal1(sK0)) | r1_tarski(sK1,k1_ordinal1(sK0)) | ~v3_ordinal1(sK1) | ~spl2_32),
% 0.20/0.55    inference(resolution,[],[f318,f36])).
% 0.20/0.55  fof(f318,plain,(
% 0.20/0.55    r1_ordinal1(sK1,k1_ordinal1(sK0)) | ~spl2_32),
% 0.20/0.55    inference(avatar_component_clause,[],[f317])).
% 0.20/0.55  fof(f409,plain,(
% 0.20/0.55    spl2_38 | ~spl2_1 | spl2_5 | ~spl2_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f391,f88,f81,f62,f371])).
% 0.20/0.55  fof(f391,plain,(
% 0.20/0.55    r2_hidden(sK1,k1_ordinal1(sK0)) | (~spl2_1 | spl2_5 | ~spl2_6)),
% 0.20/0.55    inference(subsumption_resolution,[],[f385,f163])).
% 0.20/0.55  fof(f163,plain,(
% 0.20/0.55    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | spl2_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f81])).
% 0.20/0.55  fof(f385,plain,(
% 0.20/0.55    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK1,k1_ordinal1(sK0)) | (~spl2_1 | ~spl2_6)),
% 0.20/0.55    inference(resolution,[],[f97,f63])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(k1_ordinal1(sK0),X0) | r2_hidden(X0,k1_ordinal1(sK0))) ) | ~spl2_6),
% 0.20/0.55    inference(resolution,[],[f89,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.55    inference(flattening,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,axiom,(
% 0.20/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.55  fof(f384,plain,(
% 0.20/0.55    spl2_39 | ~spl2_2 | ~spl2_6 | ~spl2_34),
% 0.20/0.55    inference(avatar_split_clause,[],[f342,f329,f88,f66,f382])).
% 0.20/0.55  fof(f329,plain,(
% 0.20/0.55    spl2_34 <=> r1_ordinal1(sK0,k1_ordinal1(sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.55  fof(f342,plain,(
% 0.20/0.55    r1_tarski(sK0,k1_ordinal1(sK0)) | (~spl2_2 | ~spl2_6 | ~spl2_34)),
% 0.20/0.55    inference(subsumption_resolution,[],[f341,f67])).
% 0.20/0.55  fof(f341,plain,(
% 0.20/0.55    r1_tarski(sK0,k1_ordinal1(sK0)) | ~v3_ordinal1(sK0) | (~spl2_6 | ~spl2_34)),
% 0.20/0.55    inference(subsumption_resolution,[],[f340,f89])).
% 0.20/0.55  fof(f340,plain,(
% 0.20/0.55    ~v3_ordinal1(k1_ordinal1(sK0)) | r1_tarski(sK0,k1_ordinal1(sK0)) | ~v3_ordinal1(sK0) | ~spl2_34),
% 0.20/0.55    inference(resolution,[],[f330,f36])).
% 0.20/0.55  fof(f330,plain,(
% 0.20/0.55    r1_ordinal1(sK0,k1_ordinal1(sK0)) | ~spl2_34),
% 0.20/0.55    inference(avatar_component_clause,[],[f329])).
% 0.20/0.55  fof(f339,plain,(
% 0.20/0.55    ~spl2_33),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f338])).
% 0.20/0.55  fof(f338,plain,(
% 0.20/0.55    $false | ~spl2_33),
% 0.20/0.55    inference(subsumption_resolution,[],[f335,f46])).
% 0.20/0.55  fof(f335,plain,(
% 0.20/0.55    r2_hidden(k1_ordinal1(sK0),k1_ordinal1(sK0)) | ~spl2_33),
% 0.20/0.55    inference(resolution,[],[f327,f39])).
% 0.20/0.55  fof(f327,plain,(
% 0.20/0.55    r2_hidden(k1_ordinal1(sK0),sK0) | ~spl2_33),
% 0.20/0.55    inference(avatar_component_clause,[],[f326])).
% 0.20/0.55  fof(f331,plain,(
% 0.20/0.55    spl2_33 | spl2_34 | ~spl2_2 | ~spl2_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f122,f88,f66,f329,f326])).
% 0.20/0.55  fof(f122,plain,(
% 0.20/0.55    r1_ordinal1(sK0,k1_ordinal1(sK0)) | r2_hidden(k1_ordinal1(sK0),sK0) | (~spl2_2 | ~spl2_6)),
% 0.20/0.55    inference(resolution,[],[f72,f89])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(sK0,X0) | r2_hidden(X0,sK0)) ) | ~spl2_2),
% 0.20/0.55    inference(resolution,[],[f67,f37])).
% 0.20/0.55  fof(f319,plain,(
% 0.20/0.55    spl2_31 | spl2_32 | ~spl2_1 | ~spl2_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f112,f88,f62,f317,f314])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    r1_ordinal1(sK1,k1_ordinal1(sK0)) | r2_hidden(k1_ordinal1(sK0),sK1) | (~spl2_1 | ~spl2_6)),
% 0.20/0.55    inference(resolution,[],[f70,f89])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(sK1,X0) | r2_hidden(X0,sK1)) ) | ~spl2_1),
% 0.20/0.55    inference(resolution,[],[f63,f37])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    spl2_15 | ~spl2_1 | ~spl2_2 | spl2_14),
% 0.20/0.55    inference(avatar_split_clause,[],[f169,f160,f66,f62,f166])).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    spl2_15 <=> r1_ordinal1(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.55  fof(f169,plain,(
% 0.20/0.55    r1_ordinal1(sK0,sK1) | (~spl2_1 | ~spl2_2 | spl2_14)),
% 0.20/0.55    inference(subsumption_resolution,[],[f119,f161])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    r1_ordinal1(sK0,sK1) | r2_hidden(sK1,sK0) | (~spl2_1 | ~spl2_2)),
% 0.20/0.55    inference(resolution,[],[f72,f63])).
% 0.20/0.55  fof(f231,plain,(
% 0.20/0.55    sK0 != sK1 | r2_hidden(sK1,sK0) | ~r2_hidden(sK0,sK1)),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    spl2_19 | ~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_13 | ~spl2_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f200,f166,f144,f81,f66,f62,f228])).
% 0.20/0.55  fof(f200,plain,(
% 0.20/0.55    r1_ordinal1(k1_ordinal1(sK0),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_13 | ~spl2_15)),
% 0.20/0.55    inference(forward_demodulation,[],[f82,f186])).
% 0.20/0.55  fof(f186,plain,(
% 0.20/0.55    sK0 = sK1 | (~spl2_1 | ~spl2_2 | ~spl2_13 | ~spl2_15)),
% 0.20/0.55    inference(subsumption_resolution,[],[f183,f178])).
% 0.20/0.55  fof(f178,plain,(
% 0.20/0.55    r1_tarski(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_15)),
% 0.20/0.55    inference(subsumption_resolution,[],[f177,f67])).
% 0.20/0.55  fof(f177,plain,(
% 0.20/0.55    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | (~spl2_1 | ~spl2_15)),
% 0.20/0.55    inference(subsumption_resolution,[],[f176,f63])).
% 0.20/0.55  fof(f176,plain,(
% 0.20/0.55    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl2_15),
% 0.20/0.55    inference(resolution,[],[f167,f36])).
% 0.20/0.55  fof(f167,plain,(
% 0.20/0.55    r1_ordinal1(sK0,sK1) | ~spl2_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f166])).
% 0.20/0.55  fof(f183,plain,(
% 0.20/0.55    ~r1_tarski(sK0,sK1) | sK0 = sK1 | ~spl2_13),
% 0.20/0.55    inference(resolution,[],[f145,f54])).
% 0.20/0.55  fof(f226,plain,(
% 0.20/0.55    ~spl2_18 | ~spl2_13 | spl2_14 | ~spl2_16),
% 0.20/0.55    inference(avatar_split_clause,[],[f222,f195,f160,f144,f224])).
% 0.20/0.55  fof(f195,plain,(
% 0.20/0.55    spl2_16 <=> r1_tarski(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.55  fof(f222,plain,(
% 0.20/0.55    ~r2_hidden(sK0,sK0) | (~spl2_13 | spl2_14 | ~spl2_16)),
% 0.20/0.55    inference(forward_demodulation,[],[f161,f205])).
% 0.20/0.55  fof(f205,plain,(
% 0.20/0.55    sK0 = sK1 | (~spl2_13 | ~spl2_16)),
% 0.20/0.55    inference(subsumption_resolution,[],[f183,f196])).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    r1_tarski(sK0,sK1) | ~spl2_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f195])).
% 0.20/0.55  fof(f204,plain,(
% 0.20/0.55    spl2_17 | ~spl2_1 | ~spl2_2 | ~spl2_13 | ~spl2_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f186,f166,f144,f66,f62,f202])).
% 0.20/0.55  fof(f197,plain,(
% 0.20/0.55    spl2_16 | ~spl2_1 | ~spl2_2 | ~spl2_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f178,f166,f66,f62,f195])).
% 0.20/0.55  fof(f164,plain,(
% 0.20/0.55    ~spl2_5 | ~spl2_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f153,f78,f81])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    spl2_4 <=> r2_hidden(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.55  fof(f153,plain,(
% 0.20/0.55    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~spl2_4),
% 0.20/0.55    inference(subsumption_resolution,[],[f32,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    r2_hidden(sK0,sK1) | ~spl2_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f78])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,negated_conjecture,(
% 0.20/0.55    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.55    inference(negated_conjecture,[],[f19])).
% 0.20/0.55  fof(f19,conjecture,(
% 0.20/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    ~spl2_14 | ~spl2_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f155,f78,f160])).
% 0.20/0.55  fof(f155,plain,(
% 0.20/0.55    ~r2_hidden(sK1,sK0) | ~spl2_4),
% 0.20/0.55    inference(resolution,[],[f79,f46])).
% 0.20/0.55  fof(f127,plain,(
% 0.20/0.55    spl2_10 | ~spl2_1 | ~spl2_2 | spl2_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f114,f78,f66,f62,f125])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    r1_ordinal1(sK1,sK0) | (~spl2_1 | ~spl2_2 | spl2_4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f110,f85])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ~r2_hidden(sK0,sK1) | spl2_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f78])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    r1_ordinal1(sK1,sK0) | r2_hidden(sK0,sK1) | (~spl2_1 | ~spl2_2)),
% 0.20/0.55    inference(resolution,[],[f70,f67])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    spl2_6 | ~spl2_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f71,f66,f88])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    v3_ordinal1(k1_ordinal1(sK0)) | ~spl2_2),
% 0.20/0.55    inference(resolution,[],[f67,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,axiom,(
% 0.20/0.55    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    spl2_4 | spl2_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f31,f81,f78])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    spl2_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f34,f66])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    v3_ordinal1(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    spl2_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f33,f62])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    v3_ordinal1(sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (16494)------------------------------
% 0.20/0.55  % (16494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (16494)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (16494)Memory used [KB]: 6524
% 0.20/0.55  % (16494)Time elapsed: 0.143 s
% 0.20/0.55  % (16494)------------------------------
% 0.20/0.55  % (16494)------------------------------
% 0.20/0.55  % (16464)Success in time 0.186 s
%------------------------------------------------------------------------------
