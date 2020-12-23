%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_0__t3_xboole_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:18 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 208 expanded)
%              Number of leaves         :   18 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  326 ( 963 expanded)
%              Number of equality atoms :   35 (  86 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f712,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f77,f278,f593,f607,f614,f711])).

fof(f711,plain,(
    ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f708])).

fof(f708,plain,
    ( $false
    | ~ spl5_14 ),
    inference(resolution,[],[f626,f39])).

fof(f39,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',dt_o_0_0_xboole_0)).

fof(f626,plain,
    ( ! [X3] : ~ v1_xboole_0(X3)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f625,f260])).

fof(f260,plain,(
    ! [X8,X7] :
      ( r1_xboole_0(X7,X8)
      | ~ v1_xboole_0(X7) ) ),
    inference(subsumption_resolution,[],[f246,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',l13_xboole_0)).

fof(f246,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 != X7
      | r1_xboole_0(X7,X8)
      | ~ v1_xboole_0(X7) ) ),
    inference(superposition,[],[f48,f223])).

fof(f223,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X4,X5) = X4
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f120,f41])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',d1_xboole_0)).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',d4_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',d7_xboole_0)).

fof(f625,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(X3)
        | ~ r1_xboole_0(X3,X4) )
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f218,f620])).

fof(f620,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_14 ),
    inference(resolution,[],[f277,f41])).

fof(f277,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl5_14
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f218,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X3)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f184,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f184,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k3_xboole_0(X2,X3))
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f102,f41])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k3_xboole_0(X0,X1)),X0)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f57,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f614,plain,
    ( ~ spl5_2
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f609,f63])).

fof(f63,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f609,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(resolution,[],[f75,f274])).

fof(f274,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK2,X4)
        | ~ r1_xboole_0(X4,sK1) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl5_12
  <=> ! [X4] :
        ( ~ r2_hidden(sK2,X4)
        | ~ r1_xboole_0(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f75,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_6
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f607,plain,
    ( ~ spl5_0
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f606])).

fof(f606,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f75,f283])).

fof(f283,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(resolution,[],[f60,f67])).

fof(f67,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f60,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_0
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f593,plain,
    ( ~ spl5_0
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f586])).

fof(f586,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_3 ),
    inference(resolution,[],[f528,f39])).

fof(f528,plain,
    ( ! [X6] : ~ v1_xboole_0(X6)
    | ~ spl5_0
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f527,f40])).

fof(f527,plain,
    ( ! [X6] :
        ( k1_xboole_0 != X6
        | ~ v1_xboole_0(X6) )
    | ~ spl5_0
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f508,f71])).

fof(f71,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_3
  <=> ~ r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f508,plain,
    ( ! [X6] :
        ( k1_xboole_0 != X6
        | r1_xboole_0(sK0,sK1)
        | ~ v1_xboole_0(X6) )
    | ~ spl5_0 ),
    inference(superposition,[],[f48,f483])).

fof(f483,plain,
    ( ! [X0] :
        ( k3_xboole_0(sK0,sK1) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl5_0 ),
    inference(forward_demodulation,[],[f481,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',commutativity_k3_xboole_0)).

fof(f481,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k3_xboole_0(sK1,sK0) = X0 )
    | ~ spl5_0 ),
    inference(duplicate_literal_removal,[],[f468])).

fof(f468,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k3_xboole_0(sK1,sK0) = X0
        | k3_xboole_0(sK1,sK0) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f305,f122])).

fof(f122,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(X3,X4,X5),X4)
      | k3_xboole_0(X3,X4) = X5
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f305,plain,
    ( ! [X30,X31] :
        ( ~ r2_hidden(sK4(sK1,X30,X31),sK0)
        | ~ v1_xboole_0(X31)
        | k3_xboole_0(sK1,X30) = X31 )
    | ~ spl5_0 ),
    inference(resolution,[],[f117,f60])).

fof(f117,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(X3,X4,X5),X3)
      | k3_xboole_0(X3,X4) = X5
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f52,f41])).

fof(f278,plain,
    ( spl5_12
    | spl5_14
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f263,f66,f276,f273])).

fof(f263,plain,
    ( ! [X4] :
        ( r2_hidden(sK2,k1_xboole_0)
        | ~ r2_hidden(sK2,X4)
        | ~ r1_xboole_0(X4,sK1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f112,f67])).

fof(f112,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,X3)
      | r2_hidden(X4,k1_xboole_0)
      | ~ r2_hidden(X4,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f55,f47])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,
    ( ~ spl5_3
    | spl5_6 ),
    inference(avatar_split_clause,[],[f33,f74,f70])).

fof(f33,plain,
    ( r2_hidden(sK2,sK0)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( r1_xboole_0(sK0,sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK2,sK0) )
    | ( ! [X3] :
          ( ~ r2_hidden(X3,sK1)
          | ~ r2_hidden(X3,sK0) )
      & ~ r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
        | ( ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) )
   => ( ( r1_xboole_0(sK0,sK1)
        & ? [X2] :
            ( r2_hidden(X2,sK1)
            & r2_hidden(X2,sK0) ) )
      | ( ! [X3] :
            ( ~ r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK0) )
        & ~ r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( r2_hidden(sK2,X1)
        & r2_hidden(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] :
            ( r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      | ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X3] :
                ~ ( r2_hidden(X3,X1)
                  & r2_hidden(X3,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X2] :
                ~ ( r2_hidden(X2,X1)
                  & r2_hidden(X2,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t3_xboole_0.p',t3_xboole_0)).

fof(f76,plain,
    ( spl5_0
    | spl5_6 ),
    inference(avatar_split_clause,[],[f34,f74,f59])).

fof(f34,plain,(
    ! [X3] :
      ( r2_hidden(sK2,sK0)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f35,f66,f70])).

fof(f35,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,
    ( spl5_0
    | spl5_4 ),
    inference(avatar_split_clause,[],[f36,f66,f59])).

fof(f36,plain,(
    ! [X3] :
      ( r2_hidden(sK2,sK1)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,
    ( spl5_0
    | spl5_2 ),
    inference(avatar_split_clause,[],[f38,f62,f59])).

fof(f38,plain,(
    ! [X3] :
      ( r1_xboole_0(sK0,sK1)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
