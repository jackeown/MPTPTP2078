%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:04 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 185 expanded)
%              Number of leaves         :   23 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  332 ( 632 expanded)
%              Number of equality atoms :   74 ( 161 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2991,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f71,f76,f81,f102,f107,f113,f150,f173,f207,f271,f324,f389,f567,f2958])).

fof(f2958,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_6
    | ~ spl2_12
    | ~ spl2_28
    | ~ spl2_30
    | ~ spl2_46 ),
    inference(avatar_contradiction_clause,[],[f2957])).

fof(f2957,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | spl2_6
    | ~ spl2_12
    | ~ spl2_28
    | ~ spl2_30
    | ~ spl2_46 ),
    inference(subsumption_resolution,[],[f2956,f101])).

fof(f101,plain,
    ( sK1 != k2_funct_1(sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_6
  <=> sK1 = k2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f2956,plain,
    ( sK1 = k2_funct_1(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_28
    | ~ spl2_30
    | ~ spl2_46 ),
    inference(forward_demodulation,[],[f2955,f388])).

fof(f388,plain,
    ( sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl2_30
  <=> sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f2955,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_28
    | ~ spl2_46 ),
    inference(subsumption_resolution,[],[f2924,f60])).

fof(f60,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f2924,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_28
    | ~ spl2_46 ),
    inference(superposition,[],[f566,f1078])).

fof(f1078,plain,
    ( ! [X1] :
        ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X1) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f1065,f75])).

fof(f75,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1065,plain,
    ( ! [X1] :
        ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X1) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK0) )
    | ~ spl2_12
    | ~ spl2_28 ),
    inference(superposition,[],[f154,f323])).

fof(f323,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl2_28
  <=> k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f154,plain,
    ( ! [X2,X3] :
        ( k5_relat_1(k5_relat_1(k2_funct_1(sK0),X2),X3) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X2,X3))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl2_12 ),
    inference(resolution,[],[f149,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f149,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl2_12
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f566,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f564])).

fof(f564,plain,
    ( spl2_46
  <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f567,plain,
    ( spl2_46
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f409,f268,f147,f110,f564])).

fof(f110,plain,
    ( spl2_8
  <=> k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f268,plain,
    ( spl2_24
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f409,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1))
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f408,f112])).

fof(f112,plain,
    ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f408,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f155,f270])).

fof(f270,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f268])).

fof(f155,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl2_12 ),
    inference(resolution,[],[f149,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f389,plain,
    ( spl2_30
    | ~ spl2_1
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f239,f204,f58,f386])).

fof(f204,plain,
    ( spl2_17
  <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f239,plain,
    ( sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl2_1
    | ~ spl2_17 ),
    inference(resolution,[],[f83,f206])).

fof(f206,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f204])).

fof(f83,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK1),X1)
        | sK1 = k5_relat_1(k6_relat_1(X1),sK1) )
    | ~ spl2_1 ),
    inference(resolution,[],[f60,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f324,plain,
    ( spl2_28
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f310,f104,f78,f73,f68,f321])).

fof(f68,plain,
    ( spl2_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f78,plain,
    ( spl2_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f104,plain,
    ( spl2_7
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f310,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f309,f106])).

fof(f106,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f309,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f308,f75])).

fof(f308,plain,
    ( ~ v1_relat_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f89,f80])).

fof(f80,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f89,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f70,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f70,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f271,plain,
    ( spl2_24
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f257,f78,f73,f68,f268])).

fof(f257,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f256,f75])).

fof(f256,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f91,f80])).

fof(f91,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f70,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f207,plain,
    ( spl2_17
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f197,f170,f58,f204])).

fof(f170,plain,
    ( spl2_13
  <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f197,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f196,f60])).

fof(f196,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f193,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f193,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl2_13 ),
    inference(superposition,[],[f46,f172])).

fof(f172,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f170])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f173,plain,
    ( spl2_13
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f86,f58,f170])).

fof(f86,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_1 ),
    inference(resolution,[],[f60,f45])).

fof(f150,plain,
    ( spl2_12
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f145,f78,f73,f147])).

fof(f145,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f94,f80])).

fof(f94,plain,
    ( ~ v1_funct_1(sK0)
    | v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f113,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f36,f110])).

fof(f36,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f107,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f35,f104])).

fof(f35,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f102,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f37,f99])).

fof(f37,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f76,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (11433)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (11425)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (11432)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (11442)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (11428)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (11426)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (11437)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (11427)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (11424)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (11430)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (11429)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (11439)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (11435)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (11441)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (11423)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (11438)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (11443)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (11434)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (11436)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (11440)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (11431)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (11443)Refutation not found, incomplete strategy% (11443)------------------------------
% 0.21/0.52  % (11443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11443)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11443)Memory used [KB]: 10618
% 0.21/0.52  % (11443)Time elapsed: 0.115 s
% 0.21/0.52  % (11443)------------------------------
% 0.21/0.52  % (11443)------------------------------
% 1.60/0.56  % (11426)Refutation found. Thanks to Tanya!
% 1.60/0.56  % SZS status Theorem for theBenchmark
% 1.60/0.57  % SZS output start Proof for theBenchmark
% 1.60/0.57  fof(f2991,plain,(
% 1.60/0.57    $false),
% 1.60/0.57    inference(avatar_sat_refutation,[],[f61,f71,f76,f81,f102,f107,f113,f150,f173,f207,f271,f324,f389,f567,f2958])).
% 1.60/0.57  fof(f2958,plain,(
% 1.60/0.57    ~spl2_1 | ~spl2_4 | spl2_6 | ~spl2_12 | ~spl2_28 | ~spl2_30 | ~spl2_46),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f2957])).
% 1.60/0.57  fof(f2957,plain,(
% 1.60/0.57    $false | (~spl2_1 | ~spl2_4 | spl2_6 | ~spl2_12 | ~spl2_28 | ~spl2_30 | ~spl2_46)),
% 1.60/0.57    inference(subsumption_resolution,[],[f2956,f101])).
% 1.60/0.57  fof(f101,plain,(
% 1.60/0.57    sK1 != k2_funct_1(sK0) | spl2_6),
% 1.60/0.57    inference(avatar_component_clause,[],[f99])).
% 1.60/0.57  fof(f99,plain,(
% 1.60/0.57    spl2_6 <=> sK1 = k2_funct_1(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.60/0.57  fof(f2956,plain,(
% 1.60/0.57    sK1 = k2_funct_1(sK0) | (~spl2_1 | ~spl2_4 | ~spl2_12 | ~spl2_28 | ~spl2_30 | ~spl2_46)),
% 1.60/0.57    inference(forward_demodulation,[],[f2955,f388])).
% 1.60/0.57  fof(f388,plain,(
% 1.60/0.57    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) | ~spl2_30),
% 1.60/0.57    inference(avatar_component_clause,[],[f386])).
% 1.60/0.57  fof(f386,plain,(
% 1.60/0.57    spl2_30 <=> sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 1.60/0.57  fof(f2955,plain,(
% 1.60/0.57    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) | (~spl2_1 | ~spl2_4 | ~spl2_12 | ~spl2_28 | ~spl2_46)),
% 1.60/0.57    inference(subsumption_resolution,[],[f2924,f60])).
% 1.60/0.57  fof(f60,plain,(
% 1.60/0.57    v1_relat_1(sK1) | ~spl2_1),
% 1.60/0.57    inference(avatar_component_clause,[],[f58])).
% 1.60/0.57  fof(f58,plain,(
% 1.60/0.57    spl2_1 <=> v1_relat_1(sK1)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.60/0.57  fof(f2924,plain,(
% 1.60/0.57    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) | ~v1_relat_1(sK1) | (~spl2_4 | ~spl2_12 | ~spl2_28 | ~spl2_46)),
% 1.60/0.57    inference(superposition,[],[f566,f1078])).
% 1.60/0.57  fof(f1078,plain,(
% 1.60/0.57    ( ! [X1] : (k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X1) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X1)) | ~v1_relat_1(X1)) ) | (~spl2_4 | ~spl2_12 | ~spl2_28)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1065,f75])).
% 1.60/0.57  fof(f75,plain,(
% 1.60/0.57    v1_relat_1(sK0) | ~spl2_4),
% 1.60/0.57    inference(avatar_component_clause,[],[f73])).
% 1.60/0.57  fof(f73,plain,(
% 1.60/0.57    spl2_4 <=> v1_relat_1(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.60/0.57  fof(f1065,plain,(
% 1.60/0.57    ( ! [X1] : (k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X1) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(sK0)) ) | (~spl2_12 | ~spl2_28)),
% 1.60/0.57    inference(superposition,[],[f154,f323])).
% 1.60/0.57  fof(f323,plain,(
% 1.60/0.57    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1)) | ~spl2_28),
% 1.60/0.57    inference(avatar_component_clause,[],[f321])).
% 1.60/0.57  fof(f321,plain,(
% 1.60/0.57    spl2_28 <=> k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 1.60/0.57  fof(f154,plain,(
% 1.60/0.57    ( ! [X2,X3] : (k5_relat_1(k5_relat_1(k2_funct_1(sK0),X2),X3) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) ) | ~spl2_12),
% 1.60/0.57    inference(resolution,[],[f149,f48])).
% 1.60/0.57  fof(f48,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f21])).
% 1.60/0.57  fof(f21,plain,(
% 1.60/0.57    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.60/0.57    inference(ennf_transformation,[],[f5])).
% 1.60/0.57  fof(f5,axiom,(
% 1.60/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.60/0.57  fof(f149,plain,(
% 1.60/0.57    v1_relat_1(k2_funct_1(sK0)) | ~spl2_12),
% 1.60/0.57    inference(avatar_component_clause,[],[f147])).
% 1.60/0.57  fof(f147,plain,(
% 1.60/0.57    spl2_12 <=> v1_relat_1(k2_funct_1(sK0))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.60/0.57  fof(f566,plain,(
% 1.60/0.57    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) | ~spl2_46),
% 1.60/0.57    inference(avatar_component_clause,[],[f564])).
% 1.60/0.57  fof(f564,plain,(
% 1.60/0.57    spl2_46 <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 1.60/0.57  fof(f567,plain,(
% 1.60/0.57    spl2_46 | ~spl2_8 | ~spl2_12 | ~spl2_24),
% 1.60/0.57    inference(avatar_split_clause,[],[f409,f268,f147,f110,f564])).
% 1.60/0.57  fof(f110,plain,(
% 1.60/0.57    spl2_8 <=> k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.60/0.57  fof(f268,plain,(
% 1.60/0.57    spl2_24 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.60/0.57  fof(f409,plain,(
% 1.60/0.57    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) | (~spl2_8 | ~spl2_12 | ~spl2_24)),
% 1.60/0.57    inference(forward_demodulation,[],[f408,f112])).
% 1.60/0.57  fof(f112,plain,(
% 1.60/0.57    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) | ~spl2_8),
% 1.60/0.57    inference(avatar_component_clause,[],[f110])).
% 1.60/0.57  fof(f408,plain,(
% 1.60/0.57    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) | (~spl2_12 | ~spl2_24)),
% 1.60/0.57    inference(forward_demodulation,[],[f155,f270])).
% 1.60/0.57  fof(f270,plain,(
% 1.60/0.57    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl2_24),
% 1.60/0.57    inference(avatar_component_clause,[],[f268])).
% 1.60/0.57  fof(f155,plain,(
% 1.60/0.57    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~spl2_12),
% 1.60/0.57    inference(resolution,[],[f149,f45])).
% 1.60/0.57  fof(f45,plain,(
% 1.60/0.57    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.60/0.57    inference(cnf_transformation,[],[f18])).
% 1.60/0.57  fof(f18,plain,(
% 1.60/0.57    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.60/0.57    inference(ennf_transformation,[],[f8])).
% 1.60/0.57  fof(f8,axiom,(
% 1.60/0.57    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.60/0.57  fof(f389,plain,(
% 1.60/0.57    spl2_30 | ~spl2_1 | ~spl2_17),
% 1.60/0.57    inference(avatar_split_clause,[],[f239,f204,f58,f386])).
% 1.60/0.57  fof(f204,plain,(
% 1.60/0.57    spl2_17 <=> r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.60/0.57  fof(f239,plain,(
% 1.60/0.57    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) | (~spl2_1 | ~spl2_17)),
% 1.60/0.57    inference(resolution,[],[f83,f206])).
% 1.60/0.57  fof(f206,plain,(
% 1.60/0.57    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~spl2_17),
% 1.60/0.57    inference(avatar_component_clause,[],[f204])).
% 1.60/0.57  fof(f83,plain,(
% 1.60/0.57    ( ! [X1] : (~r1_tarski(k1_relat_1(sK1),X1) | sK1 = k5_relat_1(k6_relat_1(X1),sK1)) ) | ~spl2_1),
% 1.60/0.57    inference(resolution,[],[f60,f55])).
% 1.60/0.57  fof(f55,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 1.60/0.57    inference(cnf_transformation,[],[f29])).
% 1.60/0.57  fof(f29,plain,(
% 1.60/0.57    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.60/0.57    inference(flattening,[],[f28])).
% 1.60/0.57  fof(f28,plain,(
% 1.60/0.57    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.60/0.57    inference(ennf_transformation,[],[f7])).
% 1.60/0.57  fof(f7,axiom,(
% 1.60/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.60/0.57  fof(f324,plain,(
% 1.60/0.57    spl2_28 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_7),
% 1.60/0.57    inference(avatar_split_clause,[],[f310,f104,f78,f73,f68,f321])).
% 1.60/0.57  fof(f68,plain,(
% 1.60/0.57    spl2_3 <=> v2_funct_1(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.60/0.57  fof(f78,plain,(
% 1.60/0.57    spl2_5 <=> v1_funct_1(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.60/0.57  fof(f104,plain,(
% 1.60/0.57    spl2_7 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.60/0.57  fof(f310,plain,(
% 1.60/0.57    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_7)),
% 1.60/0.57    inference(forward_demodulation,[],[f309,f106])).
% 1.60/0.57  fof(f106,plain,(
% 1.60/0.57    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl2_7),
% 1.60/0.57    inference(avatar_component_clause,[],[f104])).
% 1.60/0.57  fof(f309,plain,(
% 1.60/0.57    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 1.60/0.57    inference(subsumption_resolution,[],[f308,f75])).
% 1.60/0.57  fof(f308,plain,(
% 1.60/0.57    ~v1_relat_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | (~spl2_3 | ~spl2_5)),
% 1.60/0.57    inference(subsumption_resolution,[],[f89,f80])).
% 1.60/0.57  fof(f80,plain,(
% 1.60/0.57    v1_funct_1(sK0) | ~spl2_5),
% 1.60/0.57    inference(avatar_component_clause,[],[f78])).
% 1.60/0.57  fof(f89,plain,(
% 1.60/0.57    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | ~spl2_3),
% 1.60/0.57    inference(resolution,[],[f70,f54])).
% 1.60/0.57  fof(f54,plain,(
% 1.60/0.57    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f27])).
% 1.60/0.57  fof(f27,plain,(
% 1.60/0.57    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.57    inference(flattening,[],[f26])).
% 1.60/0.57  fof(f26,plain,(
% 1.60/0.57    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f12])).
% 1.60/0.57  fof(f12,axiom,(
% 1.60/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.60/0.57  fof(f70,plain,(
% 1.60/0.57    v2_funct_1(sK0) | ~spl2_3),
% 1.60/0.57    inference(avatar_component_clause,[],[f68])).
% 1.60/0.57  fof(f271,plain,(
% 1.60/0.57    spl2_24 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 1.60/0.57    inference(avatar_split_clause,[],[f257,f78,f73,f68,f268])).
% 1.60/0.57  fof(f257,plain,(
% 1.60/0.57    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 1.60/0.57    inference(subsumption_resolution,[],[f256,f75])).
% 1.60/0.57  fof(f256,plain,(
% 1.60/0.57    ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | (~spl2_3 | ~spl2_5)),
% 1.60/0.57    inference(subsumption_resolution,[],[f91,f80])).
% 1.60/0.57  fof(f91,plain,(
% 1.60/0.57    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl2_3),
% 1.60/0.57    inference(resolution,[],[f70,f52])).
% 1.60/0.57  fof(f52,plain,(
% 1.60/0.57    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f25])).
% 1.60/0.57  fof(f25,plain,(
% 1.60/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.57    inference(flattening,[],[f24])).
% 1.60/0.57  fof(f24,plain,(
% 1.60/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f11])).
% 1.60/0.57  fof(f11,axiom,(
% 1.60/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.60/0.57  fof(f207,plain,(
% 1.60/0.57    spl2_17 | ~spl2_1 | ~spl2_13),
% 1.60/0.57    inference(avatar_split_clause,[],[f197,f170,f58,f204])).
% 1.60/0.57  fof(f170,plain,(
% 1.60/0.57    spl2_13 <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.60/0.57  fof(f197,plain,(
% 1.60/0.57    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | (~spl2_1 | ~spl2_13)),
% 1.60/0.57    inference(subsumption_resolution,[],[f196,f60])).
% 1.60/0.57  fof(f196,plain,(
% 1.60/0.57    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl2_13),
% 1.60/0.57    inference(subsumption_resolution,[],[f193,f40])).
% 1.60/0.57  fof(f40,plain,(
% 1.60/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f10])).
% 1.60/0.57  fof(f10,axiom,(
% 1.60/0.57    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.60/0.57  fof(f193,plain,(
% 1.60/0.57    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK1))) | ~v1_relat_1(sK1) | ~spl2_13),
% 1.60/0.57    inference(superposition,[],[f46,f172])).
% 1.60/0.57  fof(f172,plain,(
% 1.60/0.57    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_13),
% 1.60/0.57    inference(avatar_component_clause,[],[f170])).
% 1.60/0.57  fof(f46,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f19])).
% 1.60/0.57  fof(f19,plain,(
% 1.60/0.57    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.60/0.57    inference(ennf_transformation,[],[f4])).
% 1.60/0.57  fof(f4,axiom,(
% 1.60/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 1.60/0.57  fof(f173,plain,(
% 1.60/0.57    spl2_13 | ~spl2_1),
% 1.60/0.57    inference(avatar_split_clause,[],[f86,f58,f170])).
% 1.60/0.57  fof(f86,plain,(
% 1.60/0.57    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_1),
% 1.60/0.57    inference(resolution,[],[f60,f45])).
% 1.60/0.57  fof(f150,plain,(
% 1.60/0.57    spl2_12 | ~spl2_4 | ~spl2_5),
% 1.60/0.57    inference(avatar_split_clause,[],[f145,f78,f73,f147])).
% 1.60/0.57  fof(f145,plain,(
% 1.60/0.57    v1_relat_1(k2_funct_1(sK0)) | (~spl2_4 | ~spl2_5)),
% 1.60/0.57    inference(subsumption_resolution,[],[f94,f80])).
% 1.60/0.57  fof(f94,plain,(
% 1.60/0.57    ~v1_funct_1(sK0) | v1_relat_1(k2_funct_1(sK0)) | ~spl2_4),
% 1.60/0.57    inference(resolution,[],[f75,f49])).
% 1.60/0.57  fof(f49,plain,(
% 1.60/0.57    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f23])).
% 1.60/0.57  fof(f23,plain,(
% 1.60/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.57    inference(flattening,[],[f22])).
% 1.60/0.57  fof(f22,plain,(
% 1.60/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f9])).
% 1.60/0.57  fof(f9,axiom,(
% 1.60/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.60/0.57  fof(f113,plain,(
% 1.60/0.57    spl2_8),
% 1.60/0.57    inference(avatar_split_clause,[],[f36,f110])).
% 1.60/0.57  fof(f36,plain,(
% 1.60/0.57    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 1.60/0.57    inference(cnf_transformation,[],[f16])).
% 1.60/0.57  fof(f16,plain,(
% 1.60/0.57    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.60/0.57    inference(flattening,[],[f15])).
% 1.60/0.57  fof(f15,plain,(
% 1.60/0.57    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f14])).
% 1.60/0.57  fof(f14,negated_conjecture,(
% 1.60/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.60/0.57    inference(negated_conjecture,[],[f13])).
% 1.60/0.57  fof(f13,conjecture,(
% 1.60/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 1.60/0.57  fof(f107,plain,(
% 1.60/0.57    spl2_7),
% 1.60/0.57    inference(avatar_split_clause,[],[f35,f104])).
% 1.60/0.57  fof(f35,plain,(
% 1.60/0.57    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 1.60/0.57    inference(cnf_transformation,[],[f16])).
% 1.60/0.57  fof(f102,plain,(
% 1.60/0.57    ~spl2_6),
% 1.60/0.57    inference(avatar_split_clause,[],[f37,f99])).
% 1.60/0.57  fof(f37,plain,(
% 1.60/0.57    sK1 != k2_funct_1(sK0)),
% 1.60/0.57    inference(cnf_transformation,[],[f16])).
% 1.60/0.57  fof(f81,plain,(
% 1.60/0.57    spl2_5),
% 1.60/0.57    inference(avatar_split_clause,[],[f39,f78])).
% 1.60/0.57  fof(f39,plain,(
% 1.60/0.57    v1_funct_1(sK0)),
% 1.60/0.57    inference(cnf_transformation,[],[f16])).
% 1.60/0.57  fof(f76,plain,(
% 1.60/0.57    spl2_4),
% 1.60/0.57    inference(avatar_split_clause,[],[f38,f73])).
% 1.60/0.57  fof(f38,plain,(
% 1.60/0.57    v1_relat_1(sK0)),
% 1.60/0.57    inference(cnf_transformation,[],[f16])).
% 1.60/0.57  fof(f71,plain,(
% 1.60/0.57    spl2_3),
% 1.60/0.57    inference(avatar_split_clause,[],[f34,f68])).
% 1.60/0.57  fof(f34,plain,(
% 1.60/0.57    v2_funct_1(sK0)),
% 1.60/0.57    inference(cnf_transformation,[],[f16])).
% 1.60/0.57  fof(f61,plain,(
% 1.60/0.57    spl2_1),
% 1.60/0.57    inference(avatar_split_clause,[],[f32,f58])).
% 1.60/0.57  fof(f32,plain,(
% 1.60/0.57    v1_relat_1(sK1)),
% 1.60/0.57    inference(cnf_transformation,[],[f16])).
% 1.60/0.57  % SZS output end Proof for theBenchmark
% 1.60/0.57  % (11426)------------------------------
% 1.60/0.57  % (11426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (11426)Termination reason: Refutation
% 1.60/0.57  
% 1.60/0.57  % (11426)Memory used [KB]: 12409
% 1.60/0.57  % (11426)Time elapsed: 0.142 s
% 1.60/0.57  % (11426)------------------------------
% 1.60/0.57  % (11426)------------------------------
% 1.60/0.57  % (11422)Success in time 0.22 s
%------------------------------------------------------------------------------
