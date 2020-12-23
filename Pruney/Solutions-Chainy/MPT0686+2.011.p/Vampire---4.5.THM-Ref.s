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
% DateTime   : Thu Dec  3 12:53:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 125 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  241 ( 420 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f60,f68,f80,f87,f93,f110,f120,f127])).

fof(f127,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f125,f36])).

fof(f36,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl5_1
  <=> r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f125,plain,
    ( r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(resolution,[],[f119,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_18
  <=> ! [X1,X0] :
        ( r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f120,plain,
    ( spl5_18
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f115,f108,f54,f118])).

fof(f54,plain,
    ( spl5_5
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f108,plain,
    ( spl5_16
  <=> ! [X3,X2] :
        ( r1_xboole_0(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3))
        | r2_hidden(sK4(sK3(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)),k3_xboole_0(X2,X3),sK0),k3_xboole_0(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(resolution,[],[f109,f55])).

fof(f55,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f109,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK4(sK3(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)),k3_xboole_0(X2,X3),sK0),k3_xboole_0(X2,X3))
        | r1_xboole_0(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,
    ( spl5_16
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f106,f91,f66,f49,f108])).

fof(f49,plain,
    ( spl5_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f66,plain,
    ( spl5_8
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK4(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f91,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)),k10_relat_1(sK0,k3_xboole_0(X0,X1)))
        | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f106,plain,
    ( ! [X2,X3] :
        ( r1_xboole_0(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3))
        | r2_hidden(sK4(sK3(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)),k3_xboole_0(X2,X3),sK0),k3_xboole_0(X2,X3)) )
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f99,f51])).

fof(f51,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f99,plain,
    ( ! [X2,X3] :
        ( r1_xboole_0(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3))
        | r2_hidden(sK4(sK3(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)),k3_xboole_0(X2,X3),sK0),k3_xboole_0(X2,X3))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(resolution,[],[f92,f67])).

fof(f67,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
        | r2_hidden(sK4(X0,X1,X2),X1)
        | ~ v1_relat_1(X2) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)),k10_relat_1(sK0,k3_xboole_0(X0,X1)))
        | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl5_13
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f88,f85,f58,f91])).

fof(f58,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f85,plain,
    ( spl5_12
  <=> ! [X1,X0] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)),k10_relat_1(sK0,k3_xboole_0(X0,X1)))
        | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) )
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(superposition,[],[f59,f86])).

fof(f86,plain,
    ( ! [X0,X1] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f87,plain,
    ( spl5_12
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f83,f78,f49,f44,f85])).

fof(f44,plain,
    ( spl5_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f78,plain,
    ( spl5_11
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f83,plain,
    ( ! [X0,X1] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f82,f51])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(resolution,[],[f79,f46])).

fof(f46,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f79,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

fof(f68,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
            & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f60,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
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

fof(f56,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
            & r1_xboole_0(X1,X2) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2,X1] :
        ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
        & r1_xboole_0(X1,X2) )
   => ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
      & r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_xboole_0(X1,X2)
           => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).

fof(f47,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f25,f34])).

fof(f25,plain,(
    ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (21716)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (21716)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f128,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f60,f68,f80,f87,f93,f110,f120,f127])).
% 0.20/0.42  fof(f127,plain,(
% 0.20/0.42    spl5_1 | ~spl5_2 | ~spl5_18),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f126])).
% 0.20/0.42  fof(f126,plain,(
% 0.20/0.42    $false | (spl5_1 | ~spl5_2 | ~spl5_18)),
% 0.20/0.42    inference(subsumption_resolution,[],[f125,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | spl5_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    spl5_1 <=> r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.42  fof(f125,plain,(
% 0.20/0.42    r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | (~spl5_2 | ~spl5_18)),
% 0.20/0.42    inference(resolution,[],[f119,f41])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    r1_xboole_0(sK1,sK2) | ~spl5_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f39])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    spl5_2 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.42  fof(f119,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | ~spl5_18),
% 0.20/0.42    inference(avatar_component_clause,[],[f118])).
% 0.20/0.42  fof(f118,plain,(
% 0.20/0.42    spl5_18 <=> ! [X1,X0] : (r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.42  fof(f120,plain,(
% 0.20/0.42    spl5_18 | ~spl5_5 | ~spl5_16),
% 0.20/0.42    inference(avatar_split_clause,[],[f115,f108,f54,f118])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    spl5_5 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.42  fof(f108,plain,(
% 0.20/0.42    spl5_16 <=> ! [X3,X2] : (r1_xboole_0(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)) | r2_hidden(sK4(sK3(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)),k3_xboole_0(X2,X3),sK0),k3_xboole_0(X2,X3)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.42  fof(f115,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) | ~r1_xboole_0(X0,X1)) ) | (~spl5_5 | ~spl5_16)),
% 0.20/0.42    inference(resolution,[],[f109,f55])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f54])).
% 0.20/0.42  fof(f109,plain,(
% 0.20/0.42    ( ! [X2,X3] : (r2_hidden(sK4(sK3(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)),k3_xboole_0(X2,X3),sK0),k3_xboole_0(X2,X3)) | r1_xboole_0(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3))) ) | ~spl5_16),
% 0.20/0.42    inference(avatar_component_clause,[],[f108])).
% 0.20/0.42  fof(f110,plain,(
% 0.20/0.42    spl5_16 | ~spl5_4 | ~spl5_8 | ~spl5_13),
% 0.20/0.42    inference(avatar_split_clause,[],[f106,f91,f66,f49,f108])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl5_4 <=> v1_relat_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    spl5_8 <=> ! [X1,X0,X2] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.42  fof(f91,plain,(
% 0.20/0.42    spl5_13 <=> ! [X1,X0] : (r2_hidden(sK3(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)),k10_relat_1(sK0,k3_xboole_0(X0,X1))) | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.42  fof(f106,plain,(
% 0.20/0.42    ( ! [X2,X3] : (r1_xboole_0(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)) | r2_hidden(sK4(sK3(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)),k3_xboole_0(X2,X3),sK0),k3_xboole_0(X2,X3))) ) | (~spl5_4 | ~spl5_8 | ~spl5_13)),
% 0.20/0.42    inference(subsumption_resolution,[],[f99,f51])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    v1_relat_1(sK0) | ~spl5_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f49])).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    ( ! [X2,X3] : (r1_xboole_0(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)) | r2_hidden(sK4(sK3(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)),k3_xboole_0(X2,X3),sK0),k3_xboole_0(X2,X3)) | ~v1_relat_1(sK0)) ) | (~spl5_8 | ~spl5_13)),
% 0.20/0.42    inference(resolution,[],[f92,f67])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK4(X0,X1,X2),X1) | ~v1_relat_1(X2)) ) | ~spl5_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f66])).
% 0.20/0.42  fof(f92,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r2_hidden(sK3(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)),k10_relat_1(sK0,k3_xboole_0(X0,X1))) | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | ~spl5_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f91])).
% 0.20/0.42  fof(f93,plain,(
% 0.20/0.42    spl5_13 | ~spl5_6 | ~spl5_12),
% 0.20/0.42    inference(avatar_split_clause,[],[f88,f85,f58,f91])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl5_6 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    spl5_12 <=> ! [X1,X0] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r2_hidden(sK3(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)),k10_relat_1(sK0,k3_xboole_0(X0,X1))) | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | (~spl5_6 | ~spl5_12)),
% 0.20/0.42    inference(superposition,[],[f59,f86])).
% 0.20/0.42  fof(f86,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | ~spl5_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f85])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) ) | ~spl5_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f58])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl5_12 | ~spl5_3 | ~spl5_4 | ~spl5_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f83,f78,f49,f44,f85])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    spl5_3 <=> v1_funct_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    spl5_11 <=> ! [X1,X0,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | (~spl5_3 | ~spl5_4 | ~spl5_11)),
% 0.20/0.42    inference(subsumption_resolution,[],[f82,f51])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) | ~v1_relat_1(sK0)) ) | (~spl5_3 | ~spl5_11)),
% 0.20/0.42    inference(resolution,[],[f79,f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    v1_funct_1(sK0) | ~spl5_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f44])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl5_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f78])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    spl5_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f32,f78])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(flattening,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl5_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f30,f66])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(rectify,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(nnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    spl5_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f58])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(rectify,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl5_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f54])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    spl5_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f49])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    v1_relat_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14,f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) => (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,negated_conjecture,(
% 0.20/0.42    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.20/0.42    inference(negated_conjecture,[],[f4])).
% 0.20/0.42  fof(f4,conjecture,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    spl5_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f44])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    v1_funct_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl5_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f39])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    r1_xboole_0(sK1,sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ~spl5_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f34])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (21716)------------------------------
% 0.20/0.42  % (21716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (21716)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (21716)Memory used [KB]: 10618
% 0.20/0.42  % (21716)Time elapsed: 0.008 s
% 0.20/0.42  % (21716)------------------------------
% 0.20/0.42  % (21716)------------------------------
% 0.20/0.42  % (21710)Success in time 0.064 s
%------------------------------------------------------------------------------
