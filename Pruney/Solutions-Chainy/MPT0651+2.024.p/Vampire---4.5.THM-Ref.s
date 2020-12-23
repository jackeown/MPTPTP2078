%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:51 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 160 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  265 ( 463 expanded)
%              Number of equality atoms :   64 ( 132 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f442,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f77,f85,f93,f139,f145,f230,f407,f414,f441])).

fof(f441,plain,
    ( ~ spl1_6
    | ~ spl1_5
    | ~ spl1_20
    | ~ spl1_7
    | ~ spl1_8
    | spl1_35 ),
    inference(avatar_split_clause,[],[f440,f411,f90,f82,f227,f67,f74])).

fof(f74,plain,
    ( spl1_6
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f67,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f227,plain,
    ( spl1_20
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f82,plain,
    ( spl1_7
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f90,plain,
    ( spl1_8
  <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f411,plain,
    ( spl1_35
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).

fof(f440,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_7
    | ~ spl1_8
    | spl1_35 ),
    inference(forward_demodulation,[],[f439,f84])).

fof(f84,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f439,plain,
    ( ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_8
    | spl1_35 ),
    inference(trivial_inequality_removal,[],[f438])).

fof(f438,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_8
    | spl1_35 ),
    inference(forward_demodulation,[],[f437,f92])).

fof(f92,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f437,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_35 ),
    inference(superposition,[],[f413,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f413,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_35 ),
    inference(avatar_component_clause,[],[f411])).

fof(f414,plain,
    ( ~ spl1_35
    | spl1_2
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f409,f135,f52,f411])).

fof(f52,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f135,plain,
    ( spl1_14
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f409,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_2
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f54,f137])).

fof(f137,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f54,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f407,plain,(
    spl1_20 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | spl1_20 ),
    inference(unit_resulting_resolution,[],[f229,f375])).

% (13948)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f375,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(global_subsumption,[],[f44,f374])).

% (13943)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f374,plain,(
    ! [X1] :
      ( r1_tarski(X1,X1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f373,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f373,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f372])).

fof(f372,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f43,f125])).

fof(f125,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f115,f41])).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f115,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f44,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f229,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | spl1_20 ),
    inference(avatar_component_clause,[],[f227])).

fof(f230,plain,
    ( ~ spl1_20
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7
    | spl1_15 ),
    inference(avatar_split_clause,[],[f225,f142,f82,f74,f67,f227])).

fof(f142,plain,
    ( spl1_15
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f225,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7
    | spl1_15 ),
    inference(forward_demodulation,[],[f219,f84])).

fof(f219,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl1_5
    | ~ spl1_6
    | spl1_15 ),
    inference(unit_resulting_resolution,[],[f69,f76,f144,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f144,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f76,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f69,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f145,plain,
    ( ~ spl1_15
    | spl1_1
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f140,f135,f48,f142])).

fof(f48,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f140,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_1
    | ~ spl1_14 ),
    inference(backward_demodulation,[],[f50,f137])).

fof(f50,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f139,plain,
    ( ~ spl1_5
    | spl1_14
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f133,f62,f57,f135,f67])).

fof(f57,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f62,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f133,plain,
    ( ~ v2_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(resolution,[],[f42,f64])).

fof(f64,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f93,plain,
    ( spl1_8
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f86,f67,f90])).

fof(f86,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f85,plain,
    ( spl1_7
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f78,f67,f82])).

fof(f78,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f69,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,
    ( spl1_6
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f71,f67,f74])).

fof(f71,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f69,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f70,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f65,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f32,f52,f48])).

fof(f32,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:04:04 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.45  % (13946)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.18/0.47  % (13951)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.18/0.47  % (13954)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.18/0.47  % (13962)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.18/0.47  % (13952)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.18/0.47  % (13964)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.18/0.47  % (13945)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.18/0.47  % (13955)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.18/0.47  % (13949)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.18/0.47  % (13947)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.18/0.47  % (13956)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.18/0.47  % (13964)Refutation not found, incomplete strategy% (13964)------------------------------
% 0.18/0.47  % (13964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (13964)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.47  
% 0.18/0.47  % (13964)Memory used [KB]: 10618
% 0.18/0.47  % (13964)Time elapsed: 0.053 s
% 0.18/0.47  % (13964)------------------------------
% 0.18/0.47  % (13964)------------------------------
% 0.18/0.47  % (13950)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.18/0.47  % (13951)Refutation not found, incomplete strategy% (13951)------------------------------
% 0.18/0.47  % (13951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (13951)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (13951)Memory used [KB]: 10618
% 0.18/0.48  % (13951)Time elapsed: 0.087 s
% 0.18/0.48  % (13951)------------------------------
% 0.18/0.48  % (13951)------------------------------
% 0.18/0.48  % (13960)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.18/0.48  % (13947)Refutation found. Thanks to Tanya!
% 0.18/0.48  % SZS status Theorem for theBenchmark
% 0.18/0.48  % SZS output start Proof for theBenchmark
% 0.18/0.48  fof(f442,plain,(
% 0.18/0.48    $false),
% 0.18/0.48    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f77,f85,f93,f139,f145,f230,f407,f414,f441])).
% 0.18/0.48  fof(f441,plain,(
% 0.18/0.48    ~spl1_6 | ~spl1_5 | ~spl1_20 | ~spl1_7 | ~spl1_8 | spl1_35),
% 0.18/0.48    inference(avatar_split_clause,[],[f440,f411,f90,f82,f227,f67,f74])).
% 0.18/0.48  fof(f74,plain,(
% 0.18/0.48    spl1_6 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.18/0.48  fof(f67,plain,(
% 0.18/0.48    spl1_5 <=> v1_relat_1(sK0)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.18/0.48  fof(f227,plain,(
% 0.18/0.48    spl1_20 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.18/0.48  fof(f82,plain,(
% 0.18/0.48    spl1_7 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.18/0.48  fof(f90,plain,(
% 0.18/0.48    spl1_8 <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.18/0.48  fof(f411,plain,(
% 0.18/0.48    spl1_35 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).
% 0.18/0.48  fof(f440,plain,(
% 0.18/0.48    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_7 | ~spl1_8 | spl1_35)),
% 0.18/0.48    inference(forward_demodulation,[],[f439,f84])).
% 0.18/0.48  fof(f84,plain,(
% 0.18/0.48    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_7),
% 0.18/0.48    inference(avatar_component_clause,[],[f82])).
% 0.18/0.48  fof(f439,plain,(
% 0.18/0.48    ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_8 | spl1_35)),
% 0.18/0.48    inference(trivial_inequality_removal,[],[f438])).
% 0.18/0.48  fof(f438,plain,(
% 0.18/0.48    k1_relat_1(sK0) != k1_relat_1(sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_8 | spl1_35)),
% 0.18/0.48    inference(forward_demodulation,[],[f437,f92])).
% 0.18/0.48  fof(f92,plain,(
% 0.18/0.48    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_8),
% 0.18/0.48    inference(avatar_component_clause,[],[f90])).
% 0.18/0.48  fof(f437,plain,(
% 0.18/0.48    k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | spl1_35),
% 0.18/0.48    inference(superposition,[],[f413,f35])).
% 0.18/0.48  fof(f35,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f18])).
% 0.18/0.48  fof(f18,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(flattening,[],[f17])).
% 0.18/0.48  fof(f17,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f5])).
% 0.18/0.48  fof(f5,axiom,(
% 0.18/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.18/0.48  fof(f413,plain,(
% 0.18/0.48    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | spl1_35),
% 0.18/0.48    inference(avatar_component_clause,[],[f411])).
% 0.18/0.48  fof(f414,plain,(
% 0.18/0.48    ~spl1_35 | spl1_2 | ~spl1_14),
% 0.18/0.48    inference(avatar_split_clause,[],[f409,f135,f52,f411])).
% 0.18/0.48  fof(f52,plain,(
% 0.18/0.48    spl1_2 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.18/0.48  fof(f135,plain,(
% 0.18/0.48    spl1_14 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.18/0.48  fof(f409,plain,(
% 0.18/0.48    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (spl1_2 | ~spl1_14)),
% 0.18/0.48    inference(forward_demodulation,[],[f54,f137])).
% 0.18/0.48  fof(f137,plain,(
% 0.18/0.48    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_14),
% 0.18/0.48    inference(avatar_component_clause,[],[f135])).
% 0.18/0.48  fof(f54,plain,(
% 0.18/0.48    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_2),
% 0.18/0.48    inference(avatar_component_clause,[],[f52])).
% 0.18/0.48  fof(f407,plain,(
% 0.18/0.48    spl1_20),
% 0.18/0.48    inference(avatar_contradiction_clause,[],[f404])).
% 0.18/0.48  fof(f404,plain,(
% 0.18/0.48    $false | spl1_20),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f229,f375])).
% 0.18/0.48  % (13948)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.18/0.48  fof(f375,plain,(
% 0.18/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.18/0.48    inference(global_subsumption,[],[f44,f374])).
% 0.18/0.48  % (13943)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.18/0.48  fof(f374,plain,(
% 0.18/0.48    ( ! [X1] : (r1_tarski(X1,X1) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.18/0.48    inference(forward_demodulation,[],[f373,f40])).
% 0.18/0.48  fof(f40,plain,(
% 0.18/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.18/0.48    inference(cnf_transformation,[],[f6])).
% 0.18/0.48  fof(f6,axiom,(
% 0.18/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.18/0.48  fof(f373,plain,(
% 0.18/0.48    ( ! [X1] : (r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.18/0.48    inference(duplicate_literal_removal,[],[f372])).
% 0.18/0.48  fof(f372,plain,(
% 0.18/0.48    ( ! [X1] : (r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.18/0.48    inference(superposition,[],[f43,f125])).
% 0.18/0.48  fof(f125,plain,(
% 0.18/0.48    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.18/0.48    inference(forward_demodulation,[],[f115,f41])).
% 0.18/0.48  fof(f41,plain,(
% 0.18/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.18/0.48    inference(cnf_transformation,[],[f6])).
% 0.18/0.48  fof(f115,plain,(
% 0.18/0.48    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f44,f39])).
% 0.18/0.48  fof(f39,plain,(
% 0.18/0.48    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f22])).
% 0.18/0.48  fof(f22,plain,(
% 0.18/0.48    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f7])).
% 0.18/0.48  fof(f7,axiom,(
% 0.18/0.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.18/0.48  fof(f43,plain,(
% 0.18/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f25])).
% 0.18/0.48  fof(f25,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,axiom,(
% 0.18/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.18/0.48  fof(f44,plain,(
% 0.18/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f9])).
% 0.18/0.48  fof(f9,axiom,(
% 0.18/0.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.18/0.48  fof(f229,plain,(
% 0.18/0.48    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | spl1_20),
% 0.18/0.48    inference(avatar_component_clause,[],[f227])).
% 0.18/0.48  fof(f230,plain,(
% 0.18/0.48    ~spl1_20 | ~spl1_5 | ~spl1_6 | ~spl1_7 | spl1_15),
% 0.18/0.48    inference(avatar_split_clause,[],[f225,f142,f82,f74,f67,f227])).
% 0.18/0.48  fof(f142,plain,(
% 0.18/0.48    spl1_15 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.18/0.48  fof(f225,plain,(
% 0.18/0.48    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_7 | spl1_15)),
% 0.18/0.48    inference(forward_demodulation,[],[f219,f84])).
% 0.18/0.48  fof(f219,plain,(
% 0.18/0.48    ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | (~spl1_5 | ~spl1_6 | spl1_15)),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f69,f76,f144,f36])).
% 0.18/0.48  fof(f36,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f20])).
% 0.18/0.48  fof(f20,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(flattening,[],[f19])).
% 0.18/0.48  fof(f19,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f4])).
% 0.18/0.48  fof(f4,axiom,(
% 0.18/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.18/0.48  fof(f144,plain,(
% 0.18/0.48    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | spl1_15),
% 0.18/0.48    inference(avatar_component_clause,[],[f142])).
% 0.18/0.48  fof(f76,plain,(
% 0.18/0.48    v1_relat_1(k4_relat_1(sK0)) | ~spl1_6),
% 0.18/0.48    inference(avatar_component_clause,[],[f74])).
% 0.18/0.48  fof(f69,plain,(
% 0.18/0.48    v1_relat_1(sK0) | ~spl1_5),
% 0.18/0.48    inference(avatar_component_clause,[],[f67])).
% 0.18/0.48  fof(f145,plain,(
% 0.18/0.48    ~spl1_15 | spl1_1 | ~spl1_14),
% 0.18/0.48    inference(avatar_split_clause,[],[f140,f135,f48,f142])).
% 0.18/0.48  fof(f48,plain,(
% 0.18/0.48    spl1_1 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.18/0.48  fof(f140,plain,(
% 0.18/0.48    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (spl1_1 | ~spl1_14)),
% 0.18/0.48    inference(backward_demodulation,[],[f50,f137])).
% 0.18/0.48  fof(f50,plain,(
% 0.18/0.48    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_1),
% 0.18/0.48    inference(avatar_component_clause,[],[f48])).
% 0.18/0.48  fof(f139,plain,(
% 0.18/0.48    ~spl1_5 | spl1_14 | ~spl1_3 | ~spl1_4),
% 0.18/0.48    inference(avatar_split_clause,[],[f133,f62,f57,f135,f67])).
% 0.18/0.48  fof(f57,plain,(
% 0.18/0.48    spl1_3 <=> v2_funct_1(sK0)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.18/0.48  fof(f62,plain,(
% 0.18/0.48    spl1_4 <=> v1_funct_1(sK0)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.18/0.48  fof(f133,plain,(
% 0.18/0.48    ~v2_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.18/0.48    inference(resolution,[],[f42,f64])).
% 0.18/0.48  fof(f64,plain,(
% 0.18/0.48    v1_funct_1(sK0) | ~spl1_4),
% 0.18/0.48    inference(avatar_component_clause,[],[f62])).
% 0.18/0.48  fof(f42,plain,(
% 0.18/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f24])).
% 0.18/0.48  fof(f24,plain,(
% 0.18/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(flattening,[],[f23])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.48    inference(ennf_transformation,[],[f8])).
% 0.18/0.48  fof(f8,axiom,(
% 0.18/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.18/0.48  fof(f93,plain,(
% 0.18/0.48    spl1_8 | ~spl1_5),
% 0.18/0.48    inference(avatar_split_clause,[],[f86,f67,f90])).
% 0.18/0.48  fof(f86,plain,(
% 0.18/0.48    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f69,f38])).
% 0.18/0.48  fof(f38,plain,(
% 0.18/0.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f21])).
% 0.18/0.48  fof(f21,plain,(
% 0.18/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f2])).
% 0.18/0.48  fof(f2,axiom,(
% 0.18/0.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.18/0.48  fof(f85,plain,(
% 0.18/0.48    spl1_7 | ~spl1_5),
% 0.18/0.48    inference(avatar_split_clause,[],[f78,f67,f82])).
% 0.18/0.48  fof(f78,plain,(
% 0.18/0.48    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f69,f37])).
% 0.18/0.48  fof(f37,plain,(
% 0.18/0.48    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f21])).
% 0.18/0.48  fof(f77,plain,(
% 0.18/0.48    spl1_6 | ~spl1_5),
% 0.18/0.48    inference(avatar_split_clause,[],[f71,f67,f74])).
% 0.18/0.48  fof(f71,plain,(
% 0.18/0.48    v1_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f69,f46])).
% 0.18/0.48  fof(f46,plain,(
% 0.18/0.48    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f26])).
% 0.18/0.48  fof(f26,plain,(
% 0.18/0.48    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f1])).
% 0.18/0.48  fof(f1,axiom,(
% 0.18/0.48    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.18/0.48  fof(f70,plain,(
% 0.18/0.48    spl1_5),
% 0.18/0.48    inference(avatar_split_clause,[],[f29,f67])).
% 0.18/0.48  fof(f29,plain,(
% 0.18/0.48    v1_relat_1(sK0)),
% 0.18/0.48    inference(cnf_transformation,[],[f28])).
% 0.18/0.48  fof(f28,plain,(
% 0.18/0.48    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).
% 0.18/0.48  fof(f27,plain,(
% 0.18/0.48    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f14,plain,(
% 0.18/0.48    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.18/0.48    inference(flattening,[],[f13])).
% 0.18/0.48  fof(f13,plain,(
% 0.18/0.48    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.18/0.48    inference(ennf_transformation,[],[f12])).
% 0.18/0.48  fof(f12,negated_conjecture,(
% 0.18/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.18/0.48    inference(negated_conjecture,[],[f11])).
% 0.18/0.48  fof(f11,conjecture,(
% 0.18/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.18/0.48  fof(f65,plain,(
% 0.18/0.48    spl1_4),
% 0.18/0.48    inference(avatar_split_clause,[],[f30,f62])).
% 0.18/0.48  fof(f30,plain,(
% 0.18/0.48    v1_funct_1(sK0)),
% 0.18/0.48    inference(cnf_transformation,[],[f28])).
% 0.18/0.48  fof(f60,plain,(
% 0.18/0.48    spl1_3),
% 0.18/0.48    inference(avatar_split_clause,[],[f31,f57])).
% 0.18/0.48  fof(f31,plain,(
% 0.18/0.48    v2_funct_1(sK0)),
% 0.18/0.48    inference(cnf_transformation,[],[f28])).
% 0.18/0.48  fof(f55,plain,(
% 0.18/0.48    ~spl1_1 | ~spl1_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f32,f52,f48])).
% 0.18/0.48  fof(f32,plain,(
% 0.18/0.48    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.18/0.48    inference(cnf_transformation,[],[f28])).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (13947)------------------------------
% 0.18/0.48  % (13947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (13947)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (13947)Memory used [KB]: 11001
% 0.18/0.48  % (13947)Time elapsed: 0.087 s
% 0.18/0.48  % (13947)------------------------------
% 0.18/0.48  % (13947)------------------------------
% 0.18/0.48  % (13943)Refutation not found, incomplete strategy% (13943)------------------------------
% 0.18/0.48  % (13943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (13943)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (13943)Memory used [KB]: 10618
% 0.18/0.48  % (13943)Time elapsed: 0.086 s
% 0.18/0.48  % (13943)------------------------------
% 0.18/0.48  % (13943)------------------------------
% 0.18/0.48  % (13937)Success in time 0.143 s
%------------------------------------------------------------------------------
