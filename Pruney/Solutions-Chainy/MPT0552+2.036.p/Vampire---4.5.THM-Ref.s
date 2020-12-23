%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 186 expanded)
%              Number of leaves         :   19 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  244 ( 464 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f51,f68,f115,f134,f143,f154,f179,f203,f238,f243])).

fof(f243,plain,
    ( ~ spl4_1
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl4_1
    | spl4_19 ),
    inference(subsumption_resolution,[],[f241,f43])).

fof(f43,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f241,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_19 ),
    inference(resolution,[],[f237,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f237,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl4_19
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f238,plain,
    ( ~ spl4_19
    | ~ spl4_1
    | spl4_15 ),
    inference(avatar_split_clause,[],[f207,f200,f41,f235])).

fof(f200,plain,
    ( spl4_15
  <=> r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f207,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl4_1
    | spl4_15 ),
    inference(resolution,[],[f202,f58])).

fof(f58,plain,
    ( ! [X8,X9] :
        ( r1_tarski(k7_relat_1(sK2,k3_xboole_0(X8,X9)),k7_relat_1(sK2,X8))
        | ~ v1_relat_1(k7_relat_1(sK2,X8)) )
    | ~ spl4_1 ),
    inference(superposition,[],[f32,f45])).

fof(f45,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl4_1 ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f202,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f200])).

fof(f203,plain,
    ( ~ spl4_15
    | ~ spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f177,f61,f41,f200])).

fof(f61,plain,
    ( spl4_3
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f177,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0))
    | ~ spl4_1
    | spl4_3 ),
    inference(resolution,[],[f63,f104])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f103,f43])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))
        | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f93,f31])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(sK2,X0))
        | ~ r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))
        | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) )
    | ~ spl4_1 ),
    inference(superposition,[],[f90,f46])).

fof(f46,plain,
    ( ! [X2] : k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)
    | ~ spl4_1 ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f90,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k9_relat_1(sK2,X1))
        | ~ r1_tarski(X0,k7_relat_1(sK2,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f89,f43])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k9_relat_1(sK2,X1))
        | ~ r1_tarski(X0,k7_relat_1(sK2,X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f52,f31])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(sK2,X0))
        | r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0))
        | ~ r1_tarski(X1,k7_relat_1(sK2,X0))
        | ~ v1_relat_1(X1) )
    | ~ spl4_1 ),
    inference(superposition,[],[f28,f46])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f63,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f179,plain,
    ( spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f173,f140,f127])).

fof(f127,plain,
    ( spl4_9
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f140,plain,
    ( spl4_11
  <=> r2_hidden(sK3(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f173,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl4_11 ),
    inference(resolution,[],[f142,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f142,plain,
    ( r2_hidden(sK3(sK1,sK1),sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f154,plain,
    ( ~ spl4_1
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl4_1
    | spl4_10 ),
    inference(subsumption_resolution,[],[f151,f43])).

fof(f151,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_10 ),
    inference(resolution,[],[f133,f32])).

fof(f133,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_10
  <=> r1_tarski(k7_relat_1(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f143,plain,
    ( spl4_11
    | spl4_9 ),
    inference(avatar_split_clause,[],[f138,f127,f140])).

fof(f138,plain,
    ( r2_hidden(sK3(sK1,sK1),sK1)
    | spl4_9 ),
    inference(resolution,[],[f129,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f129,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f134,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | ~ spl4_1
    | spl4_8 ),
    inference(avatar_split_clause,[],[f123,f112,f41,f131,f127])).

fof(f112,plain,
    ( spl4_8
  <=> r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f123,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl4_1
    | spl4_8 ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f119,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ r1_tarski(sK1,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | spl4_8 ),
    inference(resolution,[],[f114,f102])).

fof(f102,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(k7_relat_1(sK2,k3_xboole_0(X1,X2)),k7_relat_1(X0,X3))
        | ~ r1_tarski(k7_relat_1(sK2,X1),X0)
        | ~ r1_tarski(X2,X3)
        | ~ v1_relat_1(X0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f101,f43])).

fof(f101,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k7_relat_1(sK2,X1),X0)
        | ~ r1_tarski(X2,X3)
        | r1_tarski(k7_relat_1(sK2,k3_xboole_0(X1,X2)),k7_relat_1(X0,X3))
        | ~ v1_relat_1(sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f57,f31])).

fof(f57,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_relat_1(k7_relat_1(sK2,X4))
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(k7_relat_1(sK2,X4),X6)
        | ~ r1_tarski(X5,X7)
        | r1_tarski(k7_relat_1(sK2,k3_xboole_0(X4,X5)),k7_relat_1(X6,X7)) )
    | ~ spl4_1 ),
    inference(superposition,[],[f38,f45])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(f114,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f115,plain,
    ( ~ spl4_8
    | ~ spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f107,f65,f41,f112])).

fof(f65,plain,
    ( spl4_4
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f107,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1))
    | ~ spl4_1
    | spl4_4 ),
    inference(resolution,[],[f104,f67])).

fof(f67,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f68,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f54,f48,f65,f61])).

fof(f48,plain,
    ( spl4_2
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f54,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))
    | spl4_2 ),
    inference(resolution,[],[f50,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f50,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f51,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f44,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f25,f41])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (30173)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (30189)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (30179)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (30181)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (30171)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (30176)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (30187)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (30165)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (30192)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (30185)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (30167)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (30166)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (30164)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (30177)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (30184)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (30178)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (30168)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (30191)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (30185)Refutation not found, incomplete strategy% (30185)------------------------------
% 0.21/0.53  % (30185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30185)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30185)Memory used [KB]: 10618
% 0.21/0.53  % (30185)Time elapsed: 0.095 s
% 0.21/0.53  % (30185)------------------------------
% 0.21/0.53  % (30185)------------------------------
% 0.21/0.54  % (30190)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (30188)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (30163)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (30169)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (30175)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (30174)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (30183)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (30180)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (30182)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (30186)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (30170)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (30172)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (30183)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (30180)Refutation not found, incomplete strategy% (30180)------------------------------
% 0.21/0.56  % (30180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (30180)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (30180)Memory used [KB]: 10618
% 0.21/0.56  % (30180)Time elapsed: 0.158 s
% 0.21/0.56  % (30180)------------------------------
% 0.21/0.56  % (30180)------------------------------
% 0.21/0.56  % (30174)Refutation not found, incomplete strategy% (30174)------------------------------
% 0.21/0.56  % (30174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (30174)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (30174)Memory used [KB]: 10618
% 0.21/0.56  % (30174)Time elapsed: 0.159 s
% 0.21/0.56  % (30174)------------------------------
% 0.21/0.56  % (30174)------------------------------
% 1.63/0.58  % SZS output start Proof for theBenchmark
% 1.63/0.58  fof(f244,plain,(
% 1.63/0.58    $false),
% 1.63/0.58    inference(avatar_sat_refutation,[],[f44,f51,f68,f115,f134,f143,f154,f179,f203,f238,f243])).
% 1.63/0.58  fof(f243,plain,(
% 1.63/0.58    ~spl4_1 | spl4_19),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f242])).
% 1.63/0.58  fof(f242,plain,(
% 1.63/0.58    $false | (~spl4_1 | spl4_19)),
% 1.63/0.58    inference(subsumption_resolution,[],[f241,f43])).
% 1.63/0.58  fof(f43,plain,(
% 1.63/0.58    v1_relat_1(sK2) | ~spl4_1),
% 1.63/0.58    inference(avatar_component_clause,[],[f41])).
% 1.63/0.58  fof(f41,plain,(
% 1.63/0.58    spl4_1 <=> v1_relat_1(sK2)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.63/0.58  fof(f241,plain,(
% 1.63/0.58    ~v1_relat_1(sK2) | spl4_19),
% 1.63/0.58    inference(resolution,[],[f237,f31])).
% 1.63/0.58  fof(f31,plain,(
% 1.63/0.58    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f16])).
% 1.63/0.58  fof(f16,plain,(
% 1.63/0.58    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f5])).
% 1.63/0.58  fof(f5,axiom,(
% 1.63/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.63/0.58  fof(f237,plain,(
% 1.63/0.58    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl4_19),
% 1.63/0.58    inference(avatar_component_clause,[],[f235])).
% 1.63/0.58  fof(f235,plain,(
% 1.63/0.58    spl4_19 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.63/0.58  fof(f238,plain,(
% 1.63/0.58    ~spl4_19 | ~spl4_1 | spl4_15),
% 1.63/0.58    inference(avatar_split_clause,[],[f207,f200,f41,f235])).
% 1.63/0.58  fof(f200,plain,(
% 1.63/0.58    spl4_15 <=> r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.63/0.58  fof(f207,plain,(
% 1.63/0.58    ~v1_relat_1(k7_relat_1(sK2,sK0)) | (~spl4_1 | spl4_15)),
% 1.63/0.58    inference(resolution,[],[f202,f58])).
% 1.63/0.58  fof(f58,plain,(
% 1.63/0.58    ( ! [X8,X9] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X8,X9)),k7_relat_1(sK2,X8)) | ~v1_relat_1(k7_relat_1(sK2,X8))) ) | ~spl4_1),
% 1.63/0.58    inference(superposition,[],[f32,f45])).
% 1.63/0.58  fof(f45,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) ) | ~spl4_1),
% 1.63/0.58    inference(resolution,[],[f43,f37])).
% 1.63/0.58  fof(f37,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f20])).
% 1.63/0.58  fof(f20,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.63/0.58    inference(ennf_transformation,[],[f6])).
% 1.63/0.58  fof(f6,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.63/0.58  fof(f32,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f17])).
% 1.63/0.58  fof(f17,plain,(
% 1.63/0.58    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.63/0.58    inference(ennf_transformation,[],[f10])).
% 1.63/0.58  fof(f10,axiom,(
% 1.63/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.63/0.58  fof(f202,plain,(
% 1.63/0.58    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0)) | spl4_15),
% 1.63/0.58    inference(avatar_component_clause,[],[f200])).
% 1.63/0.58  fof(f203,plain,(
% 1.63/0.58    ~spl4_15 | ~spl4_1 | spl4_3),
% 1.63/0.58    inference(avatar_split_clause,[],[f177,f61,f41,f200])).
% 1.63/0.58  fof(f61,plain,(
% 1.63/0.58    spl4_3 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.63/0.58  fof(f177,plain,(
% 1.63/0.58    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK0)) | (~spl4_1 | spl4_3)),
% 1.63/0.58    inference(resolution,[],[f63,f104])).
% 1.63/0.58  fof(f104,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) ) | ~spl4_1),
% 1.63/0.58    inference(subsumption_resolution,[],[f103,f43])).
% 1.63/0.58  fof(f103,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) ) | ~spl4_1),
% 1.63/0.58    inference(resolution,[],[f93,f31])).
% 1.63/0.58  fof(f93,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK2,X0)) | ~r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | ~spl4_1),
% 1.63/0.58    inference(superposition,[],[f90,f46])).
% 1.63/0.58  fof(f46,plain,(
% 1.63/0.58    ( ! [X2] : (k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)) ) | ~spl4_1),
% 1.63/0.58    inference(resolution,[],[f43,f33])).
% 1.63/0.58  fof(f33,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f18])).
% 1.63/0.58  fof(f18,plain,(
% 1.63/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.63/0.58    inference(ennf_transformation,[],[f8])).
% 1.63/0.58  fof(f8,axiom,(
% 1.63/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.63/0.58  fof(f90,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,k7_relat_1(sK2,X1)) | ~v1_relat_1(X0)) ) | ~spl4_1),
% 1.63/0.58    inference(subsumption_resolution,[],[f89,f43])).
% 1.63/0.58  fof(f89,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,k7_relat_1(sK2,X1)) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) ) | ~spl4_1),
% 1.63/0.58    inference(resolution,[],[f52,f31])).
% 1.63/0.58  fof(f52,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK2,X0)) | r1_tarski(k2_relat_1(X1),k9_relat_1(sK2,X0)) | ~r1_tarski(X1,k7_relat_1(sK2,X0)) | ~v1_relat_1(X1)) ) | ~spl4_1),
% 1.63/0.58    inference(superposition,[],[f28,f46])).
% 1.63/0.58  fof(f28,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f15])).
% 1.63/0.58  fof(f15,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.63/0.58    inference(flattening,[],[f14])).
% 1.63/0.58  fof(f14,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f9])).
% 1.63/0.58  fof(f9,axiom,(
% 1.63/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.63/0.58  fof(f63,plain,(
% 1.63/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) | spl4_3),
% 1.63/0.58    inference(avatar_component_clause,[],[f61])).
% 1.63/0.58  fof(f179,plain,(
% 1.63/0.58    spl4_9 | ~spl4_11),
% 1.63/0.58    inference(avatar_split_clause,[],[f173,f140,f127])).
% 1.63/0.58  fof(f127,plain,(
% 1.63/0.58    spl4_9 <=> r1_tarski(sK1,sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.63/0.58  fof(f140,plain,(
% 1.63/0.58    spl4_11 <=> r2_hidden(sK3(sK1,sK1),sK1)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.63/0.58  fof(f173,plain,(
% 1.63/0.58    r1_tarski(sK1,sK1) | ~spl4_11),
% 1.63/0.58    inference(resolution,[],[f142,f36])).
% 1.63/0.58  fof(f36,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f19])).
% 1.63/0.58  fof(f19,plain,(
% 1.63/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f1])).
% 1.63/0.58  fof(f1,axiom,(
% 1.63/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.63/0.58  fof(f142,plain,(
% 1.63/0.58    r2_hidden(sK3(sK1,sK1),sK1) | ~spl4_11),
% 1.63/0.58    inference(avatar_component_clause,[],[f140])).
% 1.63/0.58  fof(f154,plain,(
% 1.63/0.58    ~spl4_1 | spl4_10),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f153])).
% 1.63/0.58  fof(f153,plain,(
% 1.63/0.58    $false | (~spl4_1 | spl4_10)),
% 1.63/0.58    inference(subsumption_resolution,[],[f151,f43])).
% 1.63/0.58  fof(f151,plain,(
% 1.63/0.58    ~v1_relat_1(sK2) | spl4_10),
% 1.63/0.58    inference(resolution,[],[f133,f32])).
% 1.63/0.58  fof(f133,plain,(
% 1.63/0.58    ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | spl4_10),
% 1.63/0.58    inference(avatar_component_clause,[],[f131])).
% 1.63/0.58  fof(f131,plain,(
% 1.63/0.58    spl4_10 <=> r1_tarski(k7_relat_1(sK2,sK0),sK2)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.63/0.58  fof(f143,plain,(
% 1.63/0.58    spl4_11 | spl4_9),
% 1.63/0.58    inference(avatar_split_clause,[],[f138,f127,f140])).
% 1.63/0.58  fof(f138,plain,(
% 1.63/0.58    r2_hidden(sK3(sK1,sK1),sK1) | spl4_9),
% 1.63/0.58    inference(resolution,[],[f129,f35])).
% 1.63/0.58  fof(f35,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f19])).
% 1.63/0.58  fof(f129,plain,(
% 1.63/0.58    ~r1_tarski(sK1,sK1) | spl4_9),
% 1.63/0.58    inference(avatar_component_clause,[],[f127])).
% 1.63/0.58  fof(f134,plain,(
% 1.63/0.58    ~spl4_9 | ~spl4_10 | ~spl4_1 | spl4_8),
% 1.63/0.58    inference(avatar_split_clause,[],[f123,f112,f41,f131,f127])).
% 1.63/0.58  fof(f112,plain,(
% 1.63/0.58    spl4_8 <=> r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.63/0.58  fof(f123,plain,(
% 1.63/0.58    ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~r1_tarski(sK1,sK1) | (~spl4_1 | spl4_8)),
% 1.63/0.58    inference(subsumption_resolution,[],[f119,f43])).
% 1.63/0.58  fof(f119,plain,(
% 1.63/0.58    ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~r1_tarski(sK1,sK1) | ~v1_relat_1(sK2) | (~spl4_1 | spl4_8)),
% 1.63/0.58    inference(resolution,[],[f114,f102])).
% 1.63/0.58  fof(f102,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X1,X2)),k7_relat_1(X0,X3)) | ~r1_tarski(k7_relat_1(sK2,X1),X0) | ~r1_tarski(X2,X3) | ~v1_relat_1(X0)) ) | ~spl4_1),
% 1.63/0.58    inference(subsumption_resolution,[],[f101,f43])).
% 1.63/0.58  fof(f101,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r1_tarski(k7_relat_1(sK2,X1),X0) | ~r1_tarski(X2,X3) | r1_tarski(k7_relat_1(sK2,k3_xboole_0(X1,X2)),k7_relat_1(X0,X3)) | ~v1_relat_1(sK2)) ) | ~spl4_1),
% 1.63/0.58    inference(resolution,[],[f57,f31])).
% 1.63/0.58  fof(f57,plain,(
% 1.63/0.58    ( ! [X6,X4,X7,X5] : (~v1_relat_1(k7_relat_1(sK2,X4)) | ~v1_relat_1(X6) | ~r1_tarski(k7_relat_1(sK2,X4),X6) | ~r1_tarski(X5,X7) | r1_tarski(k7_relat_1(sK2,k3_xboole_0(X4,X5)),k7_relat_1(X6,X7))) ) | ~spl4_1),
% 1.63/0.58    inference(superposition,[],[f38,f45])).
% 1.63/0.58  fof(f38,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~v1_relat_1(X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f22])).
% 1.63/0.58  fof(f22,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.63/0.58    inference(flattening,[],[f21])).
% 1.63/0.58  fof(f21,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.63/0.58    inference(ennf_transformation,[],[f7])).
% 1.63/0.58  fof(f7,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).
% 1.63/0.58  fof(f114,plain,(
% 1.63/0.58    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1)) | spl4_8),
% 1.63/0.58    inference(avatar_component_clause,[],[f112])).
% 1.63/0.58  fof(f115,plain,(
% 1.63/0.58    ~spl4_8 | ~spl4_1 | spl4_4),
% 1.63/0.58    inference(avatar_split_clause,[],[f107,f65,f41,f112])).
% 1.63/0.58  fof(f65,plain,(
% 1.63/0.58    spl4_4 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.63/0.58  fof(f107,plain,(
% 1.63/0.58    ~r1_tarski(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,sK1)) | (~spl4_1 | spl4_4)),
% 1.63/0.58    inference(resolution,[],[f104,f67])).
% 1.63/0.58  fof(f67,plain,(
% 1.63/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) | spl4_4),
% 1.63/0.58    inference(avatar_component_clause,[],[f65])).
% 1.63/0.58  fof(f68,plain,(
% 1.63/0.58    ~spl4_3 | ~spl4_4 | spl4_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f54,f48,f65,f61])).
% 1.63/0.58  fof(f48,plain,(
% 1.63/0.58    spl4_2 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.63/0.58  fof(f54,plain,(
% 1.63/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) | spl4_2),
% 1.63/0.58    inference(resolution,[],[f50,f39])).
% 1.63/0.58  fof(f39,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f24])).
% 1.63/0.58  fof(f24,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.63/0.58    inference(flattening,[],[f23])).
% 1.63/0.58  fof(f23,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.63/0.58    inference(ennf_transformation,[],[f2])).
% 1.63/0.58  fof(f2,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.63/0.58  fof(f50,plain,(
% 1.63/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) | spl4_2),
% 1.63/0.58    inference(avatar_component_clause,[],[f48])).
% 1.63/0.58  fof(f51,plain,(
% 1.63/0.58    ~spl4_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f26,f48])).
% 1.63/0.58  fof(f26,plain,(
% 1.63/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 1.63/0.58    inference(cnf_transformation,[],[f13])).
% 1.63/0.58  fof(f13,plain,(
% 1.63/0.58    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 1.63/0.58    inference(ennf_transformation,[],[f12])).
% 1.63/0.58  fof(f12,negated_conjecture,(
% 1.63/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.63/0.58    inference(negated_conjecture,[],[f11])).
% 1.63/0.58  fof(f11,conjecture,(
% 1.63/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 1.63/0.58  fof(f44,plain,(
% 1.63/0.58    spl4_1),
% 1.63/0.58    inference(avatar_split_clause,[],[f25,f41])).
% 1.63/0.58  fof(f25,plain,(
% 1.63/0.58    v1_relat_1(sK2)),
% 1.63/0.58    inference(cnf_transformation,[],[f13])).
% 1.63/0.58  % SZS output end Proof for theBenchmark
% 1.63/0.58  % (30183)------------------------------
% 1.63/0.58  % (30183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (30183)Termination reason: Refutation
% 1.63/0.58  
% 1.63/0.58  % (30183)Memory used [KB]: 10874
% 1.63/0.58  % (30183)Time elapsed: 0.157 s
% 1.63/0.58  % (30183)------------------------------
% 1.63/0.58  % (30183)------------------------------
% 1.63/0.58  % (30162)Success in time 0.22 s
%------------------------------------------------------------------------------
