%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 152 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :    7
%              Number of atoms          :  271 ( 454 expanded)
%              Number of equality atoms :   54 ( 101 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f688,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f54,f58,f62,f66,f70,f74,f78,f89,f100,f109,f227,f237,f272,f275,f317,f665,f687])).

fof(f687,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_118 ),
    inference(avatar_contradiction_clause,[],[f686])).

fof(f686,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_118 ),
    inference(subsumption_resolution,[],[f685,f34])).

fof(f34,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f685,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ spl3_3
    | ~ spl3_118 ),
    inference(resolution,[],[f664,f43])).

fof(f43,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f664,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X0) )
    | ~ spl3_118 ),
    inference(avatar_component_clause,[],[f663])).

fof(f663,plain,
    ( spl3_118
  <=> ! [X0] :
        ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X0)
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).

fof(f665,plain,
    ( spl3_118
    | ~ spl3_17
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f659,f315,f107,f663])).

fof(f107,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f315,plain,
    ( spl3_56
  <=> ! [X5] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X5)
        | k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f659,plain,
    ( ! [X0] :
        ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X0)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl3_17
    | ~ spl3_56 ),
    inference(resolution,[],[f316,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f107])).

fof(f316,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X5)
        | k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X5) )
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f315])).

fof(f317,plain,
    ( spl3_56
    | ~ spl3_8
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f300,f269,f64,f315])).

fof(f64,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f269,plain,
    ( spl3_48
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f300,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X5)
        | k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X5) )
    | ~ spl3_8
    | ~ spl3_48 ),
    inference(resolution,[],[f271,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f271,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f269])).

fof(f275,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_46 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_6
    | spl3_46 ),
    inference(subsumption_resolution,[],[f273,f53])).

fof(f53,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f273,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_6
    | spl3_46 ),
    inference(resolution,[],[f262,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f262,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl3_46
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f272,plain,
    ( ~ spl3_46
    | spl3_48
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f258,f56,f36,f269,f260])).

fof(f36,plain,
    ( spl3_2
  <=> k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f258,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(superposition,[],[f57,f37])).

fof(f37,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f237,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f232,f225,f41,f36])).

fof(f225,plain,
    ( spl3_40
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f232,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_40 ),
    inference(resolution,[],[f226,f43])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f225])).

fof(f227,plain,
    ( spl3_40
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f222,f72,f51,f225])).

fof(f72,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0) )
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(resolution,[],[f73,f53])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f109,plain,
    ( spl3_17
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f105,f98,f76,f107])).

fof(f76,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f98,plain,
    ( spl3_15
  <=> ! [X0] : k2_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X1) )
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(superposition,[],[f77,f99])).

fof(f99,plain,
    ( ! [X0] : k2_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X0) = X0
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f98])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f100,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f95,f87,f51,f98])).

fof(f87,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( k2_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1) = X1
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f95,plain,
    ( ! [X0] : k2_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X0) = X0
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(resolution,[],[f88,f53])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1) = X1 )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f80,f68,f60,f87])).

fof(f60,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f68,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1) = X1
        | ~ v1_relat_1(X0) )
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(resolution,[],[f69,f61])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f78,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f30,f76])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f74,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f70,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f66,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f62,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f58,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f54,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0)
      | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
    & r1_tarski(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0)
          | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
        & r1_tarski(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0)
        | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
      & r1_tarski(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
            & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f36,f32])).

fof(f24,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0)
    | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:46:03 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (29318)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (29316)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (29315)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (29321)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.45  % (29316)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f688,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f39,f44,f54,f58,f62,f66,f70,f74,f78,f89,f100,f109,f227,f237,f272,f275,f317,f665,f687])).
% 0.22/0.45  fof(f687,plain,(
% 0.22/0.45    spl3_1 | ~spl3_3 | ~spl3_118),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f686])).
% 0.22/0.45  fof(f686,plain,(
% 0.22/0.45    $false | (spl3_1 | ~spl3_3 | ~spl3_118)),
% 0.22/0.45    inference(subsumption_resolution,[],[f685,f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    spl3_1 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f685,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | (~spl3_3 | ~spl3_118)),
% 0.22/0.45    inference(resolution,[],[f664,f43])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f664,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(sK0,X0) | k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X0)) ) | ~spl3_118),
% 0.22/0.45    inference(avatar_component_clause,[],[f663])).
% 0.22/0.45  fof(f663,plain,(
% 0.22/0.45    spl3_118 <=> ! [X0] : (k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X0) | ~r1_tarski(sK0,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).
% 0.22/0.45  fof(f665,plain,(
% 0.22/0.45    spl3_118 | ~spl3_17 | ~spl3_56),
% 0.22/0.45    inference(avatar_split_clause,[],[f659,f315,f107,f663])).
% 0.22/0.45  fof(f107,plain,(
% 0.22/0.45    spl3_17 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.45  fof(f315,plain,(
% 0.22/0.45    spl3_56 <=> ! [X5] : (~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X5) | k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X5))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.22/0.45  fof(f659,plain,(
% 0.22/0.45    ( ! [X0] : (k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X0) | ~r1_tarski(sK0,X0)) ) | (~spl3_17 | ~spl3_56)),
% 0.22/0.45    inference(resolution,[],[f316,f108])).
% 0.22/0.45  fof(f108,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X1) | ~r1_tarski(X0,X1)) ) | ~spl3_17),
% 0.22/0.45    inference(avatar_component_clause,[],[f107])).
% 0.22/0.45  fof(f316,plain,(
% 0.22/0.45    ( ! [X5] : (~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X5) | k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X5)) ) | ~spl3_56),
% 0.22/0.45    inference(avatar_component_clause,[],[f315])).
% 0.22/0.45  fof(f317,plain,(
% 0.22/0.45    spl3_56 | ~spl3_8 | ~spl3_48),
% 0.22/0.45    inference(avatar_split_clause,[],[f300,f269,f64,f315])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    spl3_8 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.45  fof(f269,plain,(
% 0.22/0.45    spl3_48 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.45  fof(f300,plain,(
% 0.22/0.45    ( ! [X5] : (~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X5) | k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),X5)) ) | (~spl3_8 | ~spl3_48)),
% 0.22/0.45    inference(resolution,[],[f271,f65])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) ) | ~spl3_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f64])).
% 0.22/0.45  fof(f271,plain,(
% 0.22/0.45    v1_relat_1(k7_relat_1(sK2,sK0)) | ~spl3_48),
% 0.22/0.45    inference(avatar_component_clause,[],[f269])).
% 0.22/0.45  fof(f275,plain,(
% 0.22/0.45    ~spl3_5 | ~spl3_6 | spl3_46),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f274])).
% 0.22/0.45  fof(f274,plain,(
% 0.22/0.45    $false | (~spl3_5 | ~spl3_6 | spl3_46)),
% 0.22/0.45    inference(subsumption_resolution,[],[f273,f53])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    v1_relat_1(sK2) | ~spl3_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f51])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    spl3_5 <=> v1_relat_1(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.45  fof(f273,plain,(
% 0.22/0.45    ~v1_relat_1(sK2) | (~spl3_6 | spl3_46)),
% 0.22/0.45    inference(resolution,[],[f262,f57])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f56])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    spl3_6 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.45  fof(f262,plain,(
% 0.22/0.45    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl3_46),
% 0.22/0.45    inference(avatar_component_clause,[],[f260])).
% 0.22/0.45  fof(f260,plain,(
% 0.22/0.45    spl3_46 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.22/0.45  fof(f272,plain,(
% 0.22/0.45    ~spl3_46 | spl3_48 | ~spl3_2 | ~spl3_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f258,f56,f36,f269,f260])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    spl3_2 <=> k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f258,plain,(
% 0.22/0.45    v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | (~spl3_2 | ~spl3_6)),
% 0.22/0.45    inference(superposition,[],[f57,f37])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f36])).
% 0.22/0.45  fof(f237,plain,(
% 0.22/0.45    spl3_2 | ~spl3_3 | ~spl3_40),
% 0.22/0.45    inference(avatar_split_clause,[],[f232,f225,f41,f36])).
% 0.22/0.45  fof(f225,plain,(
% 0.22/0.45    spl3_40 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.45  fof(f232,plain,(
% 0.22/0.45    k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0) | (~spl3_3 | ~spl3_40)),
% 0.22/0.45    inference(resolution,[],[f226,f43])).
% 0.22/0.45  fof(f226,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0)) ) | ~spl3_40),
% 0.22/0.45    inference(avatar_component_clause,[],[f225])).
% 0.22/0.45  fof(f227,plain,(
% 0.22/0.45    spl3_40 | ~spl3_5 | ~spl3_10),
% 0.22/0.45    inference(avatar_split_clause,[],[f222,f72,f51,f225])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    spl3_10 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.45  fof(f222,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0)) ) | (~spl3_5 | ~spl3_10)),
% 0.22/0.45    inference(resolution,[],[f73,f53])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) ) | ~spl3_10),
% 0.22/0.45    inference(avatar_component_clause,[],[f72])).
% 0.22/0.45  fof(f109,plain,(
% 0.22/0.45    spl3_17 | ~spl3_11 | ~spl3_15),
% 0.22/0.45    inference(avatar_split_clause,[],[f105,f98,f76,f107])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    spl3_15 <=> ! [X0] : k2_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X0) = X0),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.45  fof(f105,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X1)) ) | (~spl3_11 | ~spl3_15)),
% 0.22/0.45    inference(superposition,[],[f77,f99])).
% 0.22/0.45  fof(f99,plain,(
% 0.22/0.45    ( ! [X0] : (k2_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X0) = X0) ) | ~spl3_15),
% 0.22/0.45    inference(avatar_component_clause,[],[f98])).
% 0.22/0.45  fof(f77,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl3_11),
% 0.22/0.45    inference(avatar_component_clause,[],[f76])).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    spl3_15 | ~spl3_5 | ~spl3_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f95,f87,f51,f98])).
% 0.22/0.45  fof(f87,plain,(
% 0.22/0.45    spl3_13 <=> ! [X1,X0] : (k2_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1) = X1 | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.45  fof(f95,plain,(
% 0.22/0.45    ( ! [X0] : (k2_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X0) = X0) ) | (~spl3_5 | ~spl3_13)),
% 0.22/0.45    inference(resolution,[],[f88,f53])).
% 0.22/0.45  fof(f88,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1) = X1) ) | ~spl3_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f87])).
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    spl3_13 | ~spl3_7 | ~spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f80,f68,f60,f87])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    spl3_7 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    spl3_9 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1) = X1 | ~v1_relat_1(X0)) ) | (~spl3_7 | ~spl3_9)),
% 0.22/0.45    inference(resolution,[],[f69,f61])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl3_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f60])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f68])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    spl3_11),
% 0.22/0.45    inference(avatar_split_clause,[],[f30,f76])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    spl3_10),
% 0.22/0.45    inference(avatar_split_clause,[],[f29,f72])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f28,f68])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    spl3_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f27,f64])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(flattening,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    spl3_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f60])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    spl3_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f25,f56])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    spl3_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f21,f51])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    v1_relat_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    (k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ? [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => ((k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (((k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.22/0.45    inference(negated_conjecture,[],[f7])).
% 0.22/0.45  fof(f7,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f41])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    r1_tarski(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ~spl3_1 | ~spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f24,f36,f32])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (29316)------------------------------
% 0.22/0.45  % (29316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (29316)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (29316)Memory used [KB]: 11001
% 0.22/0.45  % (29316)Time elapsed: 0.016 s
% 0.22/0.45  % (29316)------------------------------
% 0.22/0.45  % (29316)------------------------------
% 0.22/0.46  % (29310)Success in time 0.094 s
%------------------------------------------------------------------------------
