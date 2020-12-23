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
% DateTime   : Thu Dec  3 12:47:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 147 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  249 ( 355 expanded)
%              Number of equality atoms :   35 (  68 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f63,f68,f77,f121,f142,f151,f157,f182,f223,f229,f250])).

fof(f250,plain,
    ( spl1_1
    | ~ spl1_26 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl1_1
    | ~ spl1_26 ),
    inference(trivial_inequality_removal,[],[f242])).

fof(f242,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_26 ),
    inference(superposition,[],[f46,f239])).

fof(f239,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_26 ),
    inference(resolution,[],[f222,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f222,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_26 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl1_26
  <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).

fof(f46,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f229,plain,
    ( ~ spl1_18
    | ~ spl1_3
    | spl1_22 ),
    inference(avatar_split_clause,[],[f227,f206,f58,f149])).

fof(f149,plain,
    ( spl1_18
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f58,plain,
    ( spl1_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f206,plain,
    ( spl1_22
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f227,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl1_22 ),
    inference(resolution,[],[f207,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f207,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_22 ),
    inference(avatar_component_clause,[],[f206])).

fof(f223,plain,
    ( spl1_26
    | ~ spl1_22
    | ~ spl1_13
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f204,f61,f114,f206,f221])).

fof(f114,plain,
    ( spl1_13
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f61,plain,
    ( spl1_4
  <=> ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f204,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_4 ),
    inference(superposition,[],[f40,f152])).

fof(f152,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_4 ),
    inference(resolution,[],[f80,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f80,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0)) )
    | ~ spl1_4 ),
    inference(resolution,[],[f78,f39])).

fof(f78,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_relat_1(k5_relat_1(X0,k1_xboole_0)))
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(resolution,[],[f62,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f42,f34])).

fof(f34,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f62,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f182,plain,
    ( spl1_2
    | ~ spl1_17 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl1_2
    | ~ spl1_17 ),
    inference(trivial_inequality_removal,[],[f178])).

fof(f178,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_2
    | ~ spl1_17 ),
    inference(superposition,[],[f49,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_17 ),
    inference(resolution,[],[f141,f39])).

fof(f141,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl1_17
  <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f49,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f157,plain,(
    spl1_18 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl1_18 ),
    inference(resolution,[],[f150,f30])).

fof(f150,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( ~ spl1_3
    | ~ spl1_18
    | spl1_15 ),
    inference(avatar_split_clause,[],[f146,f133,f149,f58])).

fof(f133,plain,
    ( spl1_15
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f146,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_15 ),
    inference(resolution,[],[f134,f43])).

fof(f134,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f142,plain,
    ( spl1_17
    | ~ spl1_15
    | ~ spl1_13
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f131,f75,f114,f133,f140])).

fof(f75,plain,
    ( spl1_6
  <=> ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_xboole_0,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f131,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_6 ),
    inference(superposition,[],[f41,f117])).

fof(f117,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_6 ),
    inference(resolution,[],[f81,f30])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_6 ),
    inference(resolution,[],[f76,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f76,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f121,plain,(
    spl1_13 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl1_13 ),
    inference(resolution,[],[f115,f31])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f115,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f77,plain,
    ( ~ spl1_3
    | spl1_6 ),
    inference(avatar_split_clause,[],[f73,f75,f58])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f65,f32])).

fof(f32,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(superposition,[],[f37,f33])).

fof(f33,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f68,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl1_3 ),
    inference(resolution,[],[f64,f31])).

fof(f64,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_3 ),
    inference(resolution,[],[f59,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f59,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f63,plain,
    ( ~ spl1_3
    | spl1_4 ),
    inference(avatar_split_clause,[],[f56,f61,f58])).

fof(f56,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f36,f33])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f50,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f29,f48,f45])).

fof(f29,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:05:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (30520)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.49  % (30529)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.49  % (30529)Refutation not found, incomplete strategy% (30529)------------------------------
% 0.22/0.49  % (30529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (30529)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (30529)Memory used [KB]: 10490
% 0.22/0.49  % (30529)Time elapsed: 0.078 s
% 0.22/0.49  % (30529)------------------------------
% 0.22/0.49  % (30529)------------------------------
% 0.22/0.50  % (30543)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.50  % (30543)Refutation not found, incomplete strategy% (30543)------------------------------
% 0.22/0.50  % (30543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (30543)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (30543)Memory used [KB]: 10618
% 0.22/0.50  % (30543)Time elapsed: 0.049 s
% 0.22/0.50  % (30543)------------------------------
% 0.22/0.50  % (30543)------------------------------
% 0.22/0.50  % (30518)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (30522)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (30521)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (30521)Refutation not found, incomplete strategy% (30521)------------------------------
% 0.22/0.50  % (30521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (30521)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (30521)Memory used [KB]: 10490
% 0.22/0.50  % (30521)Time elapsed: 0.083 s
% 0.22/0.50  % (30521)------------------------------
% 0.22/0.50  % (30521)------------------------------
% 0.22/0.51  % (30526)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (30525)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (30526)Refutation not found, incomplete strategy% (30526)------------------------------
% 0.22/0.51  % (30526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30526)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30526)Memory used [KB]: 6012
% 0.22/0.51  % (30526)Time elapsed: 0.065 s
% 0.22/0.51  % (30526)------------------------------
% 0.22/0.51  % (30526)------------------------------
% 0.22/0.51  % (30540)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (30527)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (30539)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (30534)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (30524)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.52  % (30533)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (30536)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.52  % (30531)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (30531)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f255,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f50,f63,f68,f77,f121,f142,f151,f157,f182,f223,f229,f250])).
% 0.22/0.52  fof(f250,plain,(
% 0.22/0.52    spl1_1 | ~spl1_26),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f249])).
% 0.22/0.52  fof(f249,plain,(
% 0.22/0.52    $false | (spl1_1 | ~spl1_26)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f242])).
% 0.22/0.52  fof(f242,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_26)),
% 0.22/0.52    inference(superposition,[],[f46,f239])).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl1_26),
% 0.22/0.52    inference(resolution,[],[f222,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.52  fof(f222,plain,(
% 0.22/0.52    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_26),
% 0.22/0.52    inference(avatar_component_clause,[],[f221])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    spl1_26 <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    spl1_1 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    ~spl1_18 | ~spl1_3 | spl1_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f227,f206,f58,f149])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    spl1_18 <=> v1_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl1_3 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    spl1_22 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl1_22),
% 0.22/0.52    inference(resolution,[],[f207,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f206])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    spl1_26 | ~spl1_22 | ~spl1_13 | ~spl1_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f204,f61,f114,f206,f221])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    spl1_13 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl1_4 <=> ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_4),
% 0.22/0.52    inference(superposition,[],[f40,f152])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_4),
% 0.22/0.52    inference(resolution,[],[f80,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f13])).
% 0.22/0.52  fof(f13,conjecture,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0))) ) | ~spl1_4),
% 0.22/0.52    inference(resolution,[],[f78,f39])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0] : (v1_xboole_0(k2_relat_1(k5_relat_1(X0,k1_xboole_0))) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 0.22/0.52    inference(resolution,[],[f62,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f42,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.52    inference(flattening,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f61])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    spl1_2 | ~spl1_17),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f181])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    $false | (spl1_2 | ~spl1_17)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f178])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | (spl1_2 | ~spl1_17)),
% 0.22/0.52    inference(superposition,[],[f49,f161])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~spl1_17),
% 0.22/0.52    inference(resolution,[],[f141,f39])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f140])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    spl1_17 <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    spl1_2 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    spl1_18),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f155])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    $false | spl1_18),
% 0.22/0.52    inference(resolution,[],[f150,f30])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    ~v1_relat_1(sK0) | spl1_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f149])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    ~spl1_3 | ~spl1_18 | spl1_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f146,f133,f149,f58])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    spl1_15 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_15),
% 0.22/0.52    inference(resolution,[],[f134,f43])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f133])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    spl1_17 | ~spl1_15 | ~spl1_13 | ~spl1_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f131,f75,f114,f133,f140])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl1_6 <=> ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~r1_tarski(k1_xboole_0,k1_relat_1(X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_6),
% 0.22/0.52    inference(superposition,[],[f41,f117])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_6),
% 0.22/0.52    inference(resolution,[],[f81,f30])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_6),
% 0.22/0.52    inference(resolution,[],[f76,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f75])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    spl1_13),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    $false | spl1_13),
% 0.22/0.52    inference(resolution,[],[f115,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | spl1_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f114])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ~spl1_3 | spl1_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f73,f75,f58])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f65,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 0.22/0.52    inference(superposition,[],[f37,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    spl1_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    $false | spl1_3),
% 0.22/0.52    inference(resolution,[],[f64,f31])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ~v1_xboole_0(k1_xboole_0) | spl1_3),
% 0.22/0.52    inference(resolution,[],[f59,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ~v1_relat_1(k1_xboole_0) | spl1_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f58])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ~spl1_3 | spl1_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f56,f61,f58])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(superposition,[],[f36,f33])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ~spl1_1 | ~spl1_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f29,f48,f45])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (30531)------------------------------
% 0.22/0.52  % (30531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30531)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (30531)Memory used [KB]: 10618
% 0.22/0.52  % (30531)Time elapsed: 0.110 s
% 0.22/0.52  % (30531)------------------------------
% 0.22/0.52  % (30531)------------------------------
% 0.22/0.52  % (30515)Success in time 0.159 s
%------------------------------------------------------------------------------
