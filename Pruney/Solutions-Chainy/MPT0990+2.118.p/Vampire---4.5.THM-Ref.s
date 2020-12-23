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
% DateTime   : Thu Dec  3 13:02:49 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 425 expanded)
%              Number of leaves         :   43 ( 176 expanded)
%              Depth                    :   15
%              Number of atoms          :  961 (2184 expanded)
%              Number of equality atoms :  204 ( 584 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f570,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f112,f117,f122,f127,f137,f142,f147,f152,f158,f167,f173,f189,f262,f274,f293,f328,f395,f456,f481,f541,f553,f568])).

fof(f568,plain,
    ( ~ spl4_14
    | ~ spl4_16
    | spl4_41
    | ~ spl4_42 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_16
    | spl4_41
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f566,f188])).

fof(f188,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl4_16
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f566,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | ~ spl4_14
    | spl4_41
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f565,f540])).

fof(f540,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_41 ),
    inference(avatar_component_clause,[],[f538])).

fof(f538,plain,
    ( spl4_41
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f565,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,sK1)
    | ~ spl4_14
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f562,f166])).

fof(f166,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f562,plain,
    ( ~ v1_relat_1(sK3)
    | sK1 = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,sK1)
    | ~ spl4_42 ),
    inference(resolution,[],[f552,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = X1
      | ~ v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f86,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f552,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f550])).

fof(f550,plain,
    ( spl4_42
  <=> r1_tarski(sK1,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f553,plain,
    ( spl4_42
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f548,f401,f320,f285,f170,f164,f149,f134,f550])).

fof(f134,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f149,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f170,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f285,plain,
    ( spl4_23
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f320,plain,
    ( spl4_27
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f401,plain,
    ( spl4_37
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f548,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f547,f322])).

fof(f322,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f320])).

fof(f547,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f546,f287])).

fof(f287,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f285])).

fof(f546,plain,
    ( sK0 != k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f545,f81])).

fof(f81,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f545,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k6_relat_1(sK0))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f544,f166])).

fof(f544,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k6_relat_1(sK0))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f543,f136])).

fof(f136,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f543,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k6_relat_1(sK0))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f542,f172])).

fof(f172,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f542,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k6_relat_1(sK0))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f525,f151])).

fof(f151,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f525,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k6_relat_1(sK0))
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_37 ),
    inference(superposition,[],[f80,f403])).

fof(f403,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f401])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f541,plain,
    ( ~ spl4_41
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f536,f401,f320,f285,f170,f164,f149,f134,f94,f538])).

fof(f94,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f536,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f535,f322])).

fof(f535,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_37 ),
    inference(trivial_inequality_removal,[],[f534])).

fof(f534,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f533,f287])).

fof(f533,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f532,f172])).

fof(f532,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f531,f151])).

fof(f531,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f530,f166])).

fof(f530,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f529,f136])).

fof(f529,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f524,f96])).

fof(f96,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f524,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_37 ),
    inference(superposition,[],[f222,f403])).

fof(f222,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f65,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f481,plain,
    ( spl4_37
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f480,f392,f149,f139,f134,f124,f401])).

fof(f124,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f139,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f392,plain,
    ( spl4_35
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f480,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f479,f151])).

fof(f479,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f478,f141])).

fof(f141,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f478,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f477,f136])).

fof(f477,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f470,f126])).

fof(f126,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f470,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_35 ),
    inference(superposition,[],[f76,f394])).

fof(f394,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f392])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f456,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_34 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_34 ),
    inference(subsumption_resolution,[],[f454,f151])).

fof(f454,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_34 ),
    inference(subsumption_resolution,[],[f453,f141])).

fof(f453,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_34 ),
    inference(subsumption_resolution,[],[f452,f136])).

fof(f452,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_34 ),
    inference(subsumption_resolution,[],[f449,f126])).

fof(f449,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_34 ),
    inference(resolution,[],[f390,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f390,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_34 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl4_34
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f395,plain,
    ( ~ spl4_34
    | spl4_35
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f384,f155,f392,f388])).

fof(f155,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f384,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f214,f157])).

fof(f157,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f214,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f71,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f328,plain,
    ( spl4_27
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f327,f271,f170,f149,f109,f320])).

fof(f109,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f271,plain,
    ( spl4_22
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f327,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f326,f81])).

fof(f326,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f325,f172])).

fof(f325,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f324,f151])).

fof(f324,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f311,f111])).

fof(f111,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f311,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_22 ),
    inference(superposition,[],[f66,f273])).

fof(f273,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f271])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f293,plain,
    ( spl4_23
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f292,f259,f170,f149,f109,f285])).

fof(f259,plain,
    ( spl4_21
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f292,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f291,f81])).

fof(f291,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f290,f172])).

fof(f290,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f289,f151])).

fof(f289,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f276,f111])).

fof(f276,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_21 ),
    inference(superposition,[],[f68,f261])).

fof(f261,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f259])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f274,plain,
    ( spl4_22
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f269,f149,f144,f139,f119,f109,f99,f271])).

fof(f99,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f119,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f144,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f269,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f268,f151])).

fof(f268,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f267,f146])).

fof(f146,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f267,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f266,f141])).

fof(f266,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f265,f111])).

fof(f265,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f264,f101])).

fof(f101,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f264,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f263])).

fof(f263,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f248,f121])).

fof(f121,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f248,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f64,f73])).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f262,plain,
    ( spl4_21
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f257,f149,f144,f139,f119,f109,f99,f259])).

fof(f257,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f256,f151])).

fof(f256,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f255,f146])).

fof(f255,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f254,f141])).

fof(f254,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f253,f111])).

fof(f253,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f252,f101])).

fof(f252,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f251])).

fof(f251,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f247,f121])).

fof(f247,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f63,f73])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f189,plain,
    ( spl4_16
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f182,f124,f186])).

fof(f182,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f88,f126])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f173,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f168,f139,f170])).

fof(f168,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f160,f85])).

fof(f85,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f160,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f83,f141])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f167,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f162,f124,f164])).

fof(f162,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f159,f85])).

fof(f159,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f83,f126])).

fof(f158,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f153,f114,f155])).

fof(f114,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f153,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f116,f73])).

fof(f116,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f152,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f51,f149])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f147,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f52,f144])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f142,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f53,f139])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f137,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f54,f134])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f127,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f56,f124])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f122,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f57,f119])).

fof(f57,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f117,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f58,f114])).

fof(f58,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f112,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f59,f109])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f102,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f99])).

fof(f61,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f62,f94])).

fof(f62,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (3960)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (3966)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (3948)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (3973)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (3955)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (3965)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (3968)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (3958)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (3951)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (3967)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (3947)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (3969)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (3950)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (3949)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (3961)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (3972)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (3952)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (3976)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (3954)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (3971)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (3953)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (3975)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (3964)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (3963)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (3956)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (3963)Refutation not found, incomplete strategy% (3963)------------------------------
% 0.21/0.55  % (3963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3963)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3963)Memory used [KB]: 10746
% 0.21/0.55  % (3963)Time elapsed: 0.139 s
% 0.21/0.55  % (3963)------------------------------
% 0.21/0.55  % (3963)------------------------------
% 0.21/0.55  % (3970)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (3957)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (3959)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.47/0.56  % (3962)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.47/0.56  % (3974)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.47/0.56  % (3957)Refutation not found, incomplete strategy% (3957)------------------------------
% 1.47/0.56  % (3957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (3957)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (3957)Memory used [KB]: 10874
% 1.47/0.56  % (3957)Time elapsed: 0.154 s
% 1.47/0.56  % (3957)------------------------------
% 1.47/0.56  % (3957)------------------------------
% 1.47/0.57  % (3975)Refutation not found, incomplete strategy% (3975)------------------------------
% 1.47/0.57  % (3975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (3975)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (3975)Memory used [KB]: 10874
% 1.47/0.57  % (3975)Time elapsed: 0.165 s
% 1.47/0.57  % (3975)------------------------------
% 1.47/0.57  % (3975)------------------------------
% 1.47/0.57  % (3968)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f570,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(avatar_sat_refutation,[],[f97,f102,f112,f117,f122,f127,f137,f142,f147,f152,f158,f167,f173,f189,f262,f274,f293,f328,f395,f456,f481,f541,f553,f568])).
% 1.47/0.57  fof(f568,plain,(
% 1.47/0.57    ~spl4_14 | ~spl4_16 | spl4_41 | ~spl4_42),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f567])).
% 1.47/0.57  fof(f567,plain,(
% 1.47/0.57    $false | (~spl4_14 | ~spl4_16 | spl4_41 | ~spl4_42)),
% 1.47/0.57    inference(subsumption_resolution,[],[f566,f188])).
% 1.47/0.57  fof(f188,plain,(
% 1.47/0.57    v4_relat_1(sK3,sK1) | ~spl4_16),
% 1.47/0.57    inference(avatar_component_clause,[],[f186])).
% 1.47/0.57  fof(f186,plain,(
% 1.47/0.57    spl4_16 <=> v4_relat_1(sK3,sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.47/0.57  fof(f566,plain,(
% 1.47/0.57    ~v4_relat_1(sK3,sK1) | (~spl4_14 | spl4_41 | ~spl4_42)),
% 1.47/0.57    inference(subsumption_resolution,[],[f565,f540])).
% 1.47/0.57  fof(f540,plain,(
% 1.47/0.57    sK1 != k1_relat_1(sK3) | spl4_41),
% 1.47/0.57    inference(avatar_component_clause,[],[f538])).
% 1.47/0.57  fof(f538,plain,(
% 1.47/0.57    spl4_41 <=> sK1 = k1_relat_1(sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.47/0.57  fof(f565,plain,(
% 1.47/0.57    sK1 = k1_relat_1(sK3) | ~v4_relat_1(sK3,sK1) | (~spl4_14 | ~spl4_42)),
% 1.47/0.57    inference(subsumption_resolution,[],[f562,f166])).
% 1.47/0.57  fof(f166,plain,(
% 1.47/0.57    v1_relat_1(sK3) | ~spl4_14),
% 1.47/0.57    inference(avatar_component_clause,[],[f164])).
% 1.47/0.57  fof(f164,plain,(
% 1.47/0.57    spl4_14 <=> v1_relat_1(sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.47/0.57  fof(f562,plain,(
% 1.47/0.57    ~v1_relat_1(sK3) | sK1 = k1_relat_1(sK3) | ~v4_relat_1(sK3,sK1) | ~spl4_42),
% 1.47/0.57    inference(resolution,[],[f552,f176])).
% 1.47/0.57  fof(f176,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_relat_1(X0) = X1 | ~v4_relat_1(X0,X1)) )),
% 1.47/0.57    inference(resolution,[],[f86,f79])).
% 1.47/0.57  fof(f79,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f49])).
% 1.47/0.57  fof(f49,plain,(
% 1.47/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.57    inference(flattening,[],[f48])).
% 1.47/0.57  fof(f48,plain,(
% 1.47/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.57    inference(nnf_transformation,[],[f1])).
% 1.47/0.57  fof(f1,axiom,(
% 1.47/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.57  fof(f86,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f50])).
% 1.47/0.57  fof(f50,plain,(
% 1.47/0.57    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.47/0.57    inference(nnf_transformation,[],[f42])).
% 1.47/0.57  fof(f42,plain,(
% 1.47/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.47/0.57    inference(ennf_transformation,[],[f3])).
% 1.47/0.57  fof(f3,axiom,(
% 1.47/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.47/0.57  fof(f552,plain,(
% 1.47/0.57    r1_tarski(sK1,k1_relat_1(sK3)) | ~spl4_42),
% 1.47/0.57    inference(avatar_component_clause,[],[f550])).
% 1.47/0.57  fof(f550,plain,(
% 1.47/0.57    spl4_42 <=> r1_tarski(sK1,k1_relat_1(sK3))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.47/0.57  fof(f553,plain,(
% 1.47/0.57    spl4_42 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_27 | ~spl4_37),
% 1.47/0.57    inference(avatar_split_clause,[],[f548,f401,f320,f285,f170,f164,f149,f134,f550])).
% 1.47/0.57  fof(f134,plain,(
% 1.47/0.57    spl4_9 <=> v1_funct_1(sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.47/0.57  fof(f149,plain,(
% 1.47/0.57    spl4_12 <=> v1_funct_1(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.47/0.57  fof(f170,plain,(
% 1.47/0.57    spl4_15 <=> v1_relat_1(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.47/0.57  fof(f285,plain,(
% 1.47/0.57    spl4_23 <=> sK0 = k1_relat_1(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.47/0.57  fof(f320,plain,(
% 1.47/0.57    spl4_27 <=> sK1 = k2_relat_1(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.47/0.57  fof(f401,plain,(
% 1.47/0.57    spl4_37 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.47/0.57  fof(f548,plain,(
% 1.47/0.57    r1_tarski(sK1,k1_relat_1(sK3)) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_27 | ~spl4_37)),
% 1.47/0.57    inference(forward_demodulation,[],[f547,f322])).
% 1.47/0.57  fof(f322,plain,(
% 1.47/0.57    sK1 = k2_relat_1(sK2) | ~spl4_27),
% 1.47/0.57    inference(avatar_component_clause,[],[f320])).
% 1.47/0.57  fof(f547,plain,(
% 1.47/0.57    r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_37)),
% 1.47/0.57    inference(subsumption_resolution,[],[f546,f287])).
% 1.47/0.57  fof(f287,plain,(
% 1.47/0.57    sK0 = k1_relat_1(sK2) | ~spl4_23),
% 1.47/0.57    inference(avatar_component_clause,[],[f285])).
% 1.47/0.57  fof(f546,plain,(
% 1.47/0.57    sK0 != k1_relat_1(sK2) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_37)),
% 1.47/0.57    inference(forward_demodulation,[],[f545,f81])).
% 1.47/0.57  fof(f81,plain,(
% 1.47/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.47/0.57    inference(cnf_transformation,[],[f5])).
% 1.47/0.57  fof(f5,axiom,(
% 1.47/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.47/0.57  fof(f545,plain,(
% 1.47/0.57    k1_relat_1(sK2) != k1_relat_1(k6_relat_1(sK0)) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_37)),
% 1.47/0.57    inference(subsumption_resolution,[],[f544,f166])).
% 1.47/0.57  fof(f544,plain,(
% 1.47/0.57    k1_relat_1(sK2) != k1_relat_1(k6_relat_1(sK0)) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_37)),
% 1.47/0.57    inference(subsumption_resolution,[],[f543,f136])).
% 1.47/0.57  fof(f136,plain,(
% 1.47/0.57    v1_funct_1(sK3) | ~spl4_9),
% 1.47/0.57    inference(avatar_component_clause,[],[f134])).
% 1.47/0.57  fof(f543,plain,(
% 1.47/0.57    k1_relat_1(sK2) != k1_relat_1(k6_relat_1(sK0)) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_37)),
% 1.47/0.57    inference(subsumption_resolution,[],[f542,f172])).
% 1.47/0.57  fof(f172,plain,(
% 1.47/0.57    v1_relat_1(sK2) | ~spl4_15),
% 1.47/0.57    inference(avatar_component_clause,[],[f170])).
% 1.47/0.57  fof(f542,plain,(
% 1.47/0.57    k1_relat_1(sK2) != k1_relat_1(k6_relat_1(sK0)) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_37)),
% 1.47/0.57    inference(subsumption_resolution,[],[f525,f151])).
% 1.47/0.57  fof(f151,plain,(
% 1.47/0.57    v1_funct_1(sK2) | ~spl4_12),
% 1.47/0.57    inference(avatar_component_clause,[],[f149])).
% 1.47/0.57  fof(f525,plain,(
% 1.47/0.57    k1_relat_1(sK2) != k1_relat_1(k6_relat_1(sK0)) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_37),
% 1.47/0.57    inference(superposition,[],[f80,f403])).
% 1.47/0.57  fof(f403,plain,(
% 1.47/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_37),
% 1.47/0.57    inference(avatar_component_clause,[],[f401])).
% 1.47/0.57  fof(f80,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f40])).
% 1.47/0.57  fof(f40,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(flattening,[],[f39])).
% 1.47/0.57  fof(f39,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f6])).
% 1.47/0.57  fof(f6,axiom,(
% 1.47/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 1.47/0.57  fof(f541,plain,(
% 1.47/0.57    ~spl4_41 | spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_27 | ~spl4_37),
% 1.47/0.57    inference(avatar_split_clause,[],[f536,f401,f320,f285,f170,f164,f149,f134,f94,f538])).
% 1.47/0.57  fof(f94,plain,(
% 1.47/0.57    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.47/0.57  fof(f536,plain,(
% 1.47/0.57    sK1 != k1_relat_1(sK3) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_27 | ~spl4_37)),
% 1.47/0.57    inference(forward_demodulation,[],[f535,f322])).
% 1.47/0.57  fof(f535,plain,(
% 1.47/0.57    k1_relat_1(sK3) != k2_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_37)),
% 1.47/0.57    inference(trivial_inequality_removal,[],[f534])).
% 1.47/0.57  fof(f534,plain,(
% 1.47/0.57    k6_relat_1(sK0) != k6_relat_1(sK0) | k1_relat_1(sK3) != k2_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_37)),
% 1.47/0.57    inference(forward_demodulation,[],[f533,f287])).
% 1.47/0.57  fof(f533,plain,(
% 1.47/0.57    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK3) != k2_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_37)),
% 1.47/0.57    inference(subsumption_resolution,[],[f532,f172])).
% 1.47/0.57  fof(f532,plain,(
% 1.47/0.57    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_37)),
% 1.47/0.57    inference(subsumption_resolution,[],[f531,f151])).
% 1.47/0.57  fof(f531,plain,(
% 1.47/0.57    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_14 | ~spl4_37)),
% 1.47/0.57    inference(subsumption_resolution,[],[f530,f166])).
% 1.47/0.57  fof(f530,plain,(
% 1.47/0.57    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_37)),
% 1.47/0.57    inference(subsumption_resolution,[],[f529,f136])).
% 1.47/0.57  fof(f529,plain,(
% 1.47/0.57    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_37)),
% 1.47/0.57    inference(subsumption_resolution,[],[f524,f96])).
% 1.47/0.57  fof(f96,plain,(
% 1.47/0.57    k2_funct_1(sK2) != sK3 | spl4_1),
% 1.47/0.57    inference(avatar_component_clause,[],[f94])).
% 1.47/0.57  fof(f524,plain,(
% 1.47/0.57    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_37),
% 1.47/0.57    inference(superposition,[],[f222,f403])).
% 1.47/0.57  fof(f222,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f65,f70])).
% 1.47/0.57  fof(f70,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f32])).
% 1.47/0.57  fof(f32,plain,(
% 1.47/0.57    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(flattening,[],[f31])).
% 1.47/0.57  fof(f31,plain,(
% 1.47/0.57    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f7])).
% 1.47/0.57  fof(f7,axiom,(
% 1.47/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 1.47/0.57  fof(f65,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f26])).
% 1.47/0.57  fof(f26,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(flattening,[],[f25])).
% 1.47/0.57  fof(f25,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f10])).
% 1.47/0.57  fof(f10,axiom,(
% 1.47/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 1.47/0.57  fof(f481,plain,(
% 1.47/0.57    spl4_37 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_35),
% 1.47/0.57    inference(avatar_split_clause,[],[f480,f392,f149,f139,f134,f124,f401])).
% 1.47/0.57  fof(f124,plain,(
% 1.47/0.57    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.47/0.57  fof(f139,plain,(
% 1.47/0.57    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.47/0.57  fof(f392,plain,(
% 1.47/0.57    spl4_35 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.47/0.57  fof(f480,plain,(
% 1.47/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_35)),
% 1.47/0.57    inference(subsumption_resolution,[],[f479,f151])).
% 1.47/0.57  fof(f479,plain,(
% 1.47/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_35)),
% 1.47/0.57    inference(subsumption_resolution,[],[f478,f141])).
% 1.47/0.57  fof(f141,plain,(
% 1.47/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.47/0.57    inference(avatar_component_clause,[],[f139])).
% 1.47/0.57  fof(f478,plain,(
% 1.47/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_35)),
% 1.47/0.57    inference(subsumption_resolution,[],[f477,f136])).
% 1.47/0.57  fof(f477,plain,(
% 1.47/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_35)),
% 1.47/0.57    inference(subsumption_resolution,[],[f470,f126])).
% 1.47/0.57  fof(f126,plain,(
% 1.47/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.47/0.57    inference(avatar_component_clause,[],[f124])).
% 1.47/0.57  fof(f470,plain,(
% 1.47/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_35),
% 1.47/0.57    inference(superposition,[],[f76,f394])).
% 1.47/0.57  fof(f394,plain,(
% 1.47/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_35),
% 1.47/0.57    inference(avatar_component_clause,[],[f392])).
% 1.47/0.57  fof(f76,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f38])).
% 1.47/0.57  fof(f38,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.47/0.57    inference(flattening,[],[f37])).
% 1.47/0.57  fof(f37,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.47/0.57    inference(ennf_transformation,[],[f15])).
% 1.47/0.57  fof(f15,axiom,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.47/0.57  fof(f456,plain,(
% 1.47/0.57    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_34),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f455])).
% 1.47/0.57  fof(f455,plain,(
% 1.47/0.57    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_34)),
% 1.47/0.57    inference(subsumption_resolution,[],[f454,f151])).
% 1.47/0.57  fof(f454,plain,(
% 1.47/0.57    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_34)),
% 1.47/0.57    inference(subsumption_resolution,[],[f453,f141])).
% 1.47/0.57  fof(f453,plain,(
% 1.47/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_34)),
% 1.47/0.57    inference(subsumption_resolution,[],[f452,f136])).
% 1.47/0.57  fof(f452,plain,(
% 1.47/0.57    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_34)),
% 1.47/0.57    inference(subsumption_resolution,[],[f449,f126])).
% 1.47/0.57  fof(f449,plain,(
% 1.47/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_34),
% 1.47/0.57    inference(resolution,[],[f390,f75])).
% 1.47/0.57  fof(f75,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f36])).
% 1.47/0.57  fof(f36,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.47/0.57    inference(flattening,[],[f35])).
% 1.47/0.57  fof(f35,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.47/0.57    inference(ennf_transformation,[],[f14])).
% 1.47/0.57  fof(f14,axiom,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.47/0.57  fof(f390,plain,(
% 1.47/0.57    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_34),
% 1.47/0.57    inference(avatar_component_clause,[],[f388])).
% 1.47/0.57  fof(f388,plain,(
% 1.47/0.57    spl4_34 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.47/0.57  fof(f395,plain,(
% 1.47/0.57    ~spl4_34 | spl4_35 | ~spl4_13),
% 1.47/0.57    inference(avatar_split_clause,[],[f384,f155,f392,f388])).
% 1.47/0.57  fof(f155,plain,(
% 1.47/0.57    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.47/0.57  fof(f384,plain,(
% 1.47/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 1.47/0.57    inference(resolution,[],[f214,f157])).
% 1.47/0.57  fof(f157,plain,(
% 1.47/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.47/0.57    inference(avatar_component_clause,[],[f155])).
% 1.47/0.57  fof(f214,plain,(
% 1.47/0.57    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.47/0.57    inference(resolution,[],[f71,f84])).
% 1.47/0.57  fof(f84,plain,(
% 1.47/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f13])).
% 1.47/0.57  fof(f13,axiom,(
% 1.47/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.47/0.57  fof(f71,plain,(
% 1.47/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f47])).
% 1.47/0.57  fof(f47,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.57    inference(nnf_transformation,[],[f34])).
% 1.47/0.57  fof(f34,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.57    inference(flattening,[],[f33])).
% 1.47/0.57  fof(f33,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.47/0.57    inference(ennf_transformation,[],[f12])).
% 1.47/0.57  fof(f12,axiom,(
% 1.47/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.47/0.57  fof(f328,plain,(
% 1.47/0.57    spl4_27 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_22),
% 1.47/0.57    inference(avatar_split_clause,[],[f327,f271,f170,f149,f109,f320])).
% 1.47/0.57  fof(f109,plain,(
% 1.47/0.57    spl4_4 <=> v2_funct_1(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.47/0.57  fof(f271,plain,(
% 1.47/0.57    spl4_22 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.47/0.57  fof(f327,plain,(
% 1.47/0.57    sK1 = k2_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_22)),
% 1.47/0.57    inference(forward_demodulation,[],[f326,f81])).
% 1.47/0.57  fof(f326,plain,(
% 1.47/0.57    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_22)),
% 1.47/0.57    inference(subsumption_resolution,[],[f325,f172])).
% 1.47/0.57  fof(f325,plain,(
% 1.47/0.57    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_22)),
% 1.47/0.57    inference(subsumption_resolution,[],[f324,f151])).
% 1.47/0.57  fof(f324,plain,(
% 1.47/0.57    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_22)),
% 1.47/0.57    inference(subsumption_resolution,[],[f311,f111])).
% 1.47/0.57  fof(f111,plain,(
% 1.47/0.57    v2_funct_1(sK2) | ~spl4_4),
% 1.47/0.57    inference(avatar_component_clause,[],[f109])).
% 1.47/0.57  fof(f311,plain,(
% 1.47/0.57    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_22),
% 1.47/0.57    inference(superposition,[],[f66,f273])).
% 1.47/0.57  fof(f273,plain,(
% 1.47/0.57    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_22),
% 1.47/0.57    inference(avatar_component_clause,[],[f271])).
% 1.47/0.57  fof(f66,plain,(
% 1.47/0.57    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f28,plain,(
% 1.47/0.57    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(flattening,[],[f27])).
% 1.47/0.57  fof(f27,plain,(
% 1.47/0.57    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f9])).
% 1.47/0.57  fof(f9,axiom,(
% 1.47/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 1.47/0.57  fof(f293,plain,(
% 1.47/0.57    spl4_23 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_21),
% 1.47/0.57    inference(avatar_split_clause,[],[f292,f259,f170,f149,f109,f285])).
% 1.47/0.57  fof(f259,plain,(
% 1.47/0.57    spl4_21 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.47/0.57  fof(f292,plain,(
% 1.47/0.57    sK0 = k1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_21)),
% 1.47/0.57    inference(forward_demodulation,[],[f291,f81])).
% 1.47/0.57  fof(f291,plain,(
% 1.47/0.57    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_21)),
% 1.47/0.57    inference(subsumption_resolution,[],[f290,f172])).
% 1.47/0.57  fof(f290,plain,(
% 1.47/0.57    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_21)),
% 1.47/0.57    inference(subsumption_resolution,[],[f289,f151])).
% 1.47/0.57  fof(f289,plain,(
% 1.47/0.57    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_21)),
% 1.47/0.57    inference(subsumption_resolution,[],[f276,f111])).
% 1.47/0.57  fof(f276,plain,(
% 1.47/0.57    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_21),
% 1.47/0.57    inference(superposition,[],[f68,f261])).
% 1.47/0.57  fof(f261,plain,(
% 1.47/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_21),
% 1.47/0.57    inference(avatar_component_clause,[],[f259])).
% 1.47/0.57  fof(f68,plain,(
% 1.47/0.57    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f30])).
% 1.47/0.57  fof(f30,plain,(
% 1.47/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(flattening,[],[f29])).
% 1.47/0.57  fof(f29,plain,(
% 1.47/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f8])).
% 1.47/0.57  fof(f8,axiom,(
% 1.47/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.47/0.57  fof(f274,plain,(
% 1.47/0.57    spl4_22 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.47/0.57    inference(avatar_split_clause,[],[f269,f149,f144,f139,f119,f109,f99,f271])).
% 1.47/0.57  fof(f99,plain,(
% 1.47/0.57    spl4_2 <=> k1_xboole_0 = sK1),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.47/0.57  fof(f119,plain,(
% 1.47/0.57    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.47/0.57  fof(f144,plain,(
% 1.47/0.57    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.47/0.57  fof(f269,plain,(
% 1.47/0.57    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.47/0.57    inference(subsumption_resolution,[],[f268,f151])).
% 1.47/0.57  fof(f268,plain,(
% 1.47/0.57    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.47/0.57    inference(subsumption_resolution,[],[f267,f146])).
% 1.47/0.57  fof(f146,plain,(
% 1.47/0.57    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.47/0.57    inference(avatar_component_clause,[],[f144])).
% 1.47/0.57  fof(f267,plain,(
% 1.47/0.57    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.47/0.57    inference(subsumption_resolution,[],[f266,f141])).
% 1.47/0.57  fof(f266,plain,(
% 1.47/0.57    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.47/0.57    inference(subsumption_resolution,[],[f265,f111])).
% 1.47/0.57  fof(f265,plain,(
% 1.47/0.57    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.47/0.57    inference(subsumption_resolution,[],[f264,f101])).
% 1.47/0.57  fof(f101,plain,(
% 1.47/0.57    k1_xboole_0 != sK1 | spl4_2),
% 1.47/0.57    inference(avatar_component_clause,[],[f99])).
% 1.47/0.57  fof(f264,plain,(
% 1.47/0.57    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.47/0.57    inference(trivial_inequality_removal,[],[f263])).
% 1.47/0.57  fof(f263,plain,(
% 1.47/0.57    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.47/0.57    inference(superposition,[],[f248,f121])).
% 1.47/0.57  fof(f121,plain,(
% 1.47/0.57    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.47/0.57    inference(avatar_component_clause,[],[f119])).
% 1.47/0.57  fof(f248,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.47/0.57    inference(forward_demodulation,[],[f64,f73])).
% 1.47/0.57  fof(f73,plain,(
% 1.47/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f16])).
% 1.47/0.57  fof(f16,axiom,(
% 1.47/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.47/0.57  fof(f64,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f24])).
% 1.47/0.57  fof(f24,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.47/0.57    inference(flattening,[],[f23])).
% 1.47/0.57  fof(f23,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.47/0.57    inference(ennf_transformation,[],[f17])).
% 1.47/0.57  fof(f17,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.47/0.57  fof(f262,plain,(
% 1.47/0.57    spl4_21 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.47/0.57    inference(avatar_split_clause,[],[f257,f149,f144,f139,f119,f109,f99,f259])).
% 1.47/0.57  fof(f257,plain,(
% 1.47/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.47/0.57    inference(subsumption_resolution,[],[f256,f151])).
% 1.47/0.57  fof(f256,plain,(
% 1.47/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.47/0.57    inference(subsumption_resolution,[],[f255,f146])).
% 1.47/0.57  fof(f255,plain,(
% 1.47/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.47/0.57    inference(subsumption_resolution,[],[f254,f141])).
% 1.47/0.57  fof(f254,plain,(
% 1.47/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.47/0.57    inference(subsumption_resolution,[],[f253,f111])).
% 1.47/0.57  fof(f253,plain,(
% 1.47/0.57    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.47/0.57    inference(subsumption_resolution,[],[f252,f101])).
% 1.47/0.57  fof(f252,plain,(
% 1.47/0.57    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.47/0.57    inference(trivial_inequality_removal,[],[f251])).
% 1.47/0.57  fof(f251,plain,(
% 1.47/0.57    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.47/0.57    inference(superposition,[],[f247,f121])).
% 1.47/0.57  fof(f247,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.47/0.57    inference(forward_demodulation,[],[f63,f73])).
% 1.47/0.57  fof(f63,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f24])).
% 1.47/0.57  fof(f189,plain,(
% 1.47/0.57    spl4_16 | ~spl4_7),
% 1.47/0.57    inference(avatar_split_clause,[],[f182,f124,f186])).
% 1.47/0.57  fof(f182,plain,(
% 1.47/0.57    v4_relat_1(sK3,sK1) | ~spl4_7),
% 1.47/0.57    inference(resolution,[],[f88,f126])).
% 1.47/0.57  fof(f88,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f43])).
% 1.47/0.57  fof(f43,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.57    inference(ennf_transformation,[],[f20])).
% 1.47/0.57  fof(f20,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.47/0.57    inference(pure_predicate_removal,[],[f11])).
% 1.47/0.57  fof(f11,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.47/0.57  fof(f173,plain,(
% 1.47/0.57    spl4_15 | ~spl4_10),
% 1.47/0.57    inference(avatar_split_clause,[],[f168,f139,f170])).
% 1.47/0.57  fof(f168,plain,(
% 1.47/0.57    v1_relat_1(sK2) | ~spl4_10),
% 1.47/0.57    inference(subsumption_resolution,[],[f160,f85])).
% 1.47/0.57  fof(f85,plain,(
% 1.47/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f4])).
% 1.47/0.57  fof(f4,axiom,(
% 1.47/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.47/0.57  fof(f160,plain,(
% 1.47/0.57    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 1.47/0.57    inference(resolution,[],[f83,f141])).
% 1.47/0.57  fof(f83,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f41])).
% 1.47/0.57  fof(f41,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f2])).
% 1.47/0.57  fof(f2,axiom,(
% 1.47/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.47/0.57  fof(f167,plain,(
% 1.47/0.57    spl4_14 | ~spl4_7),
% 1.47/0.57    inference(avatar_split_clause,[],[f162,f124,f164])).
% 1.47/0.57  fof(f162,plain,(
% 1.47/0.57    v1_relat_1(sK3) | ~spl4_7),
% 1.47/0.57    inference(subsumption_resolution,[],[f159,f85])).
% 1.47/0.57  fof(f159,plain,(
% 1.47/0.57    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 1.47/0.57    inference(resolution,[],[f83,f126])).
% 1.47/0.57  fof(f158,plain,(
% 1.47/0.57    spl4_13 | ~spl4_5),
% 1.47/0.57    inference(avatar_split_clause,[],[f153,f114,f155])).
% 1.47/0.57  fof(f114,plain,(
% 1.47/0.57    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.47/0.57  fof(f153,plain,(
% 1.47/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.47/0.57    inference(backward_demodulation,[],[f116,f73])).
% 1.47/0.57  fof(f116,plain,(
% 1.47/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.47/0.57    inference(avatar_component_clause,[],[f114])).
% 1.47/0.57  fof(f152,plain,(
% 1.47/0.57    spl4_12),
% 1.47/0.57    inference(avatar_split_clause,[],[f51,f149])).
% 1.47/0.57  fof(f51,plain,(
% 1.47/0.57    v1_funct_1(sK2)),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f46,plain,(
% 1.47/0.57    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f45,f44])).
% 1.47/0.57  fof(f44,plain,(
% 1.47/0.57    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f45,plain,(
% 1.47/0.57    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f22,plain,(
% 1.47/0.57    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.47/0.57    inference(flattening,[],[f21])).
% 1.47/0.57  fof(f21,plain,(
% 1.47/0.57    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.47/0.57    inference(ennf_transformation,[],[f19])).
% 1.47/0.57  fof(f19,negated_conjecture,(
% 1.47/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.47/0.57    inference(negated_conjecture,[],[f18])).
% 1.47/0.57  fof(f18,conjecture,(
% 1.47/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.47/0.57  fof(f147,plain,(
% 1.47/0.57    spl4_11),
% 1.47/0.57    inference(avatar_split_clause,[],[f52,f144])).
% 1.47/0.57  fof(f52,plain,(
% 1.47/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f142,plain,(
% 1.47/0.57    spl4_10),
% 1.47/0.57    inference(avatar_split_clause,[],[f53,f139])).
% 1.47/0.57  fof(f53,plain,(
% 1.47/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f137,plain,(
% 1.47/0.57    spl4_9),
% 1.47/0.57    inference(avatar_split_clause,[],[f54,f134])).
% 1.47/0.57  fof(f54,plain,(
% 1.47/0.57    v1_funct_1(sK3)),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f127,plain,(
% 1.47/0.57    spl4_7),
% 1.47/0.57    inference(avatar_split_clause,[],[f56,f124])).
% 1.47/0.57  fof(f56,plain,(
% 1.47/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f122,plain,(
% 1.47/0.57    spl4_6),
% 1.47/0.57    inference(avatar_split_clause,[],[f57,f119])).
% 1.47/0.57  fof(f57,plain,(
% 1.47/0.57    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f117,plain,(
% 1.47/0.57    spl4_5),
% 1.47/0.57    inference(avatar_split_clause,[],[f58,f114])).
% 1.47/0.57  fof(f58,plain,(
% 1.47/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f112,plain,(
% 1.47/0.57    spl4_4),
% 1.47/0.57    inference(avatar_split_clause,[],[f59,f109])).
% 1.47/0.57  fof(f59,plain,(
% 1.47/0.57    v2_funct_1(sK2)),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f102,plain,(
% 1.47/0.57    ~spl4_2),
% 1.47/0.57    inference(avatar_split_clause,[],[f61,f99])).
% 1.47/0.57  fof(f61,plain,(
% 1.47/0.57    k1_xboole_0 != sK1),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  fof(f97,plain,(
% 1.47/0.57    ~spl4_1),
% 1.47/0.57    inference(avatar_split_clause,[],[f62,f94])).
% 1.47/0.57  fof(f62,plain,(
% 1.47/0.57    k2_funct_1(sK2) != sK3),
% 1.47/0.57    inference(cnf_transformation,[],[f46])).
% 1.47/0.57  % SZS output end Proof for theBenchmark
% 1.47/0.57  % (3968)------------------------------
% 1.47/0.57  % (3968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (3968)Termination reason: Refutation
% 1.47/0.57  
% 1.47/0.57  % (3968)Memory used [KB]: 6652
% 1.47/0.57  % (3968)Time elapsed: 0.151 s
% 1.47/0.57  % (3968)------------------------------
% 1.47/0.57  % (3968)------------------------------
% 1.47/0.57  % (3946)Success in time 0.211 s
%------------------------------------------------------------------------------
