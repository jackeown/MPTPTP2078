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
% DateTime   : Thu Dec  3 12:40:38 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 283 expanded)
%              Number of leaves         :   23 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :  403 (1110 expanded)
%              Number of equality atoms :  148 ( 588 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f104,f1130,f1132,f1144,f1169,f1203])).

fof(f1203,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f1202])).

fof(f1202,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1200,f1183])).

fof(f1183,plain,
    ( ! [X0,X1] : ~ r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,X0,X1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f93,f102,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f102,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f93,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1200,plain,
    ( r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_1 ),
    inference(superposition,[],[f75,f97])).

fof(f97,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_1
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f75,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1169,plain,
    ( spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1168])).

fof(f1168,plain,
    ( $false
    | spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1158,f208])).

fof(f208,plain,
    ( r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl5_5
  <=> r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1158,plain,
    ( ~ r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f107,f195,f49])).

fof(f195,plain,
    ( r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl5_3
  <=> r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f107,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f101,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f68])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f101,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1144,plain,
    ( spl5_5
    | spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1143,f96,f197,f206])).

fof(f197,plain,
    ( spl5_4
  <=> r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1143,plain,
    ( r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl5_1 ),
    inference(forward_demodulation,[],[f477,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f477,plain,
    ( r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0)))
    | spl5_1 ),
    inference(forward_demodulation,[],[f476,f73])).

fof(f476,plain,
    ( r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0)))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f470,f89])).

fof(f89,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f62,f68])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f470,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0)))
    | spl5_1 ),
    inference(superposition,[],[f168,f74])).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f40,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f168,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k5_xboole_0(sK0,X1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
        | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),X1) )
    | spl5_1 ),
    inference(superposition,[],[f123,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f123,plain,
    ( ~ r2_hidden(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f98,f98,f98,f94])).

fof(f94,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f1132,plain,
    ( spl5_3
    | spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1057,f96,f197,f193])).

fof(f1057,plain,
    ( r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),sK0)
    | spl5_1 ),
    inference(forward_demodulation,[],[f487,f73])).

fof(f487,plain,
    ( r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),sK0)
    | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0)))
    | spl5_1 ),
    inference(forward_demodulation,[],[f486,f73])).

fof(f486,plain,
    ( r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),sK0)
    | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0)))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f480,f89])).

fof(f480,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),sK0)
    | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0)))
    | spl5_1 ),
    inference(superposition,[],[f241,f74])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k3_enumset1(k5_xboole_0(sK0,X0),k5_xboole_0(sK0,X0),k5_xboole_0(sK0,X0),k5_xboole_0(sK0,X0),k5_xboole_0(sK0,X0)))
        | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),sK0)
        | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),X0) )
    | spl5_1 ),
    inference(superposition,[],[f132,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f132,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f98,f98,f98,f94])).

fof(f1130,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f1129])).

fof(f1129,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1127,f199])).

fof(f199,plain,
    ( r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f197])).

fof(f1127,plain,
    ( ~ r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0)
    | ~ spl5_4 ),
    inference(superposition,[],[f367,f73])).

fof(f367,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f75,f199,f49])).

fof(f104,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f72,f100,f96])).

fof(f72,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f37,f46,f70])).

fof(f37,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f103,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f71,f100,f96])).

fof(f71,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f38,f46,f70])).

fof(f38,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (31221)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (31214)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (31201)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (31205)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (31206)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (31217)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.52  % (31210)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.52  % (31208)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.53  % (31209)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.53  % (31224)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.54  % (31222)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.54  % (31202)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.54  % (31208)Refutation not found, incomplete strategy% (31208)------------------------------
% 1.36/0.54  % (31208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (31202)Refutation not found, incomplete strategy% (31202)------------------------------
% 1.36/0.54  % (31202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (31202)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (31202)Memory used [KB]: 10746
% 1.36/0.54  % (31202)Time elapsed: 0.126 s
% 1.36/0.54  % (31202)------------------------------
% 1.36/0.54  % (31202)------------------------------
% 1.36/0.54  % (31208)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (31208)Memory used [KB]: 10618
% 1.36/0.54  % (31208)Time elapsed: 0.112 s
% 1.36/0.54  % (31208)------------------------------
% 1.36/0.54  % (31208)------------------------------
% 1.36/0.54  % (31210)Refutation not found, incomplete strategy% (31210)------------------------------
% 1.36/0.54  % (31210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (31210)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (31210)Memory used [KB]: 10618
% 1.36/0.54  % (31210)Time elapsed: 0.125 s
% 1.36/0.54  % (31215)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.54  % (31210)------------------------------
% 1.36/0.54  % (31210)------------------------------
% 1.36/0.54  % (31211)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (31226)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (31211)Refutation not found, incomplete strategy% (31211)------------------------------
% 1.36/0.54  % (31211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (31211)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (31211)Memory used [KB]: 10618
% 1.36/0.54  % (31211)Time elapsed: 0.113 s
% 1.36/0.54  % (31211)------------------------------
% 1.36/0.54  % (31211)------------------------------
% 1.36/0.55  % (31218)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.56  % (31204)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.56  % (31203)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.56  % (31200)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.57  % (31227)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.57  % (31225)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.57  % (31216)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.57  % (31219)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.58  % (31228)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.58  % (31223)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.58  % (31229)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.58  % (31207)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.59  % (31220)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.59  % (31212)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.59  % (31213)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.96/0.65  % (31232)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.96/0.65  % (31226)Refutation found. Thanks to Tanya!
% 1.96/0.65  % SZS status Theorem for theBenchmark
% 1.96/0.65  % SZS output start Proof for theBenchmark
% 1.96/0.65  fof(f1204,plain,(
% 1.96/0.65    $false),
% 1.96/0.65    inference(avatar_sat_refutation,[],[f103,f104,f1130,f1132,f1144,f1169,f1203])).
% 1.96/0.65  fof(f1203,plain,(
% 1.96/0.65    ~spl5_1 | ~spl5_2),
% 1.96/0.65    inference(avatar_contradiction_clause,[],[f1202])).
% 1.96/0.65  fof(f1202,plain,(
% 1.96/0.65    $false | (~spl5_1 | ~spl5_2)),
% 1.96/0.65    inference(subsumption_resolution,[],[f1200,f1183])).
% 1.96/0.65  fof(f1183,plain,(
% 1.96/0.65    ( ! [X0,X1] : (~r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,X0,X1))) ) | ~spl5_2),
% 1.96/0.65    inference(unit_resulting_resolution,[],[f93,f102,f49])).
% 1.96/0.65  fof(f49,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f26])).
% 1.96/0.65  fof(f26,plain,(
% 1.96/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.96/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f25])).
% 1.96/0.65  fof(f25,plain,(
% 1.96/0.65    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.96/0.65    introduced(choice_axiom,[])).
% 1.96/0.65  fof(f19,plain,(
% 1.96/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.96/0.65    inference(ennf_transformation,[],[f17])).
% 1.96/0.65  fof(f17,plain,(
% 1.96/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.96/0.65    inference(rectify,[],[f3])).
% 1.96/0.65  fof(f3,axiom,(
% 1.96/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.96/0.65  fof(f102,plain,(
% 1.96/0.65    r2_hidden(sK1,sK0) | ~spl5_2),
% 1.96/0.65    inference(avatar_component_clause,[],[f100])).
% 1.96/0.65  fof(f100,plain,(
% 1.96/0.65    spl5_2 <=> r2_hidden(sK1,sK0)),
% 1.96/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.96/0.65  fof(f93,plain,(
% 1.96/0.65    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 1.96/0.65    inference(equality_resolution,[],[f92])).
% 1.96/0.65  fof(f92,plain,(
% 1.96/0.65    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 1.96/0.65    inference(equality_resolution,[],[f83])).
% 1.96/0.65  fof(f83,plain,(
% 1.96/0.65    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.96/0.65    inference(definition_unfolding,[],[f60,f68])).
% 1.96/0.65  fof(f68,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.96/0.65    inference(definition_unfolding,[],[f51,f58])).
% 1.96/0.65  fof(f58,plain,(
% 1.96/0.65    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f13])).
% 1.96/0.66  fof(f13,axiom,(
% 1.96/0.66    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.96/0.66  fof(f51,plain,(
% 1.96/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.96/0.66    inference(cnf_transformation,[],[f12])).
% 1.96/0.66  fof(f12,axiom,(
% 1.96/0.66    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.96/0.66  fof(f60,plain,(
% 1.96/0.66    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.96/0.66    inference(cnf_transformation,[],[f36])).
% 1.96/0.66  fof(f36,plain,(
% 1.96/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.96/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 1.96/0.66  fof(f35,plain,(
% 1.96/0.66    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.96/0.66    introduced(choice_axiom,[])).
% 1.96/0.66  fof(f34,plain,(
% 1.96/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.96/0.66    inference(rectify,[],[f33])).
% 1.96/0.66  fof(f33,plain,(
% 1.96/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.96/0.66    inference(flattening,[],[f32])).
% 1.96/0.66  fof(f32,plain,(
% 1.96/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.96/0.66    inference(nnf_transformation,[],[f21])).
% 1.96/0.66  fof(f21,plain,(
% 1.96/0.66    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.96/0.66    inference(ennf_transformation,[],[f9])).
% 1.96/0.66  fof(f9,axiom,(
% 1.96/0.66    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.96/0.66  fof(f1200,plain,(
% 1.96/0.66    r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl5_1),
% 1.96/0.66    inference(superposition,[],[f75,f97])).
% 1.96/0.66  fof(f97,plain,(
% 1.96/0.66    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl5_1),
% 1.96/0.66    inference(avatar_component_clause,[],[f96])).
% 1.96/0.66  fof(f96,plain,(
% 1.96/0.66    spl5_1 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.96/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.96/0.66  fof(f75,plain,(
% 1.96/0.66    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.96/0.66    inference(definition_unfolding,[],[f42,f46])).
% 1.96/0.66  fof(f46,plain,(
% 1.96/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.96/0.66    inference(cnf_transformation,[],[f4])).
% 1.96/0.66  fof(f4,axiom,(
% 1.96/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.96/0.66  fof(f42,plain,(
% 1.96/0.66    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.96/0.66    inference(cnf_transformation,[],[f7])).
% 1.96/0.66  fof(f7,axiom,(
% 1.96/0.66    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.96/0.66  fof(f1169,plain,(
% 1.96/0.66    spl5_2 | ~spl5_3 | ~spl5_5),
% 1.96/0.66    inference(avatar_contradiction_clause,[],[f1168])).
% 1.96/0.66  fof(f1168,plain,(
% 1.96/0.66    $false | (spl5_2 | ~spl5_3 | ~spl5_5)),
% 1.96/0.66    inference(subsumption_resolution,[],[f1158,f208])).
% 1.96/0.66  fof(f208,plain,(
% 1.96/0.66    r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl5_5),
% 1.96/0.66    inference(avatar_component_clause,[],[f206])).
% 1.96/0.66  fof(f206,plain,(
% 1.96/0.66    spl5_5 <=> r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.96/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.96/0.66  fof(f1158,plain,(
% 1.96/0.66    ~r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | (spl5_2 | ~spl5_3)),
% 1.96/0.66    inference(unit_resulting_resolution,[],[f107,f195,f49])).
% 1.96/0.66  fof(f195,plain,(
% 1.96/0.66    r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),sK0) | ~spl5_3),
% 1.96/0.66    inference(avatar_component_clause,[],[f193])).
% 1.96/0.66  fof(f193,plain,(
% 1.96/0.66    spl5_3 <=> r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),sK0)),
% 1.96/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.96/0.66  fof(f107,plain,(
% 1.96/0.66    r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | spl5_2),
% 1.96/0.66    inference(unit_resulting_resolution,[],[f101,f76])).
% 1.96/0.66  fof(f76,plain,(
% 1.96/0.66    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.96/0.66    inference(definition_unfolding,[],[f50,f70])).
% 1.96/0.66  fof(f70,plain,(
% 1.96/0.66    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.96/0.66    inference(definition_unfolding,[],[f41,f69])).
% 1.96/0.66  fof(f69,plain,(
% 1.96/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.96/0.66    inference(definition_unfolding,[],[f44,f68])).
% 1.96/0.66  fof(f44,plain,(
% 1.96/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.96/0.66    inference(cnf_transformation,[],[f11])).
% 1.96/0.66  fof(f11,axiom,(
% 1.96/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.96/0.66  fof(f41,plain,(
% 1.96/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.96/0.66    inference(cnf_transformation,[],[f10])).
% 1.96/0.66  fof(f10,axiom,(
% 1.96/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.96/0.66  fof(f50,plain,(
% 1.96/0.66    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.96/0.66    inference(cnf_transformation,[],[f20])).
% 1.96/0.66  fof(f20,plain,(
% 1.96/0.66    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.96/0.66    inference(ennf_transformation,[],[f14])).
% 1.96/0.66  fof(f14,axiom,(
% 1.96/0.66    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.96/0.66  fof(f101,plain,(
% 1.96/0.66    ~r2_hidden(sK1,sK0) | spl5_2),
% 1.96/0.66    inference(avatar_component_clause,[],[f100])).
% 1.96/0.66  fof(f1144,plain,(
% 1.96/0.66    spl5_5 | spl5_4 | spl5_1),
% 1.96/0.66    inference(avatar_split_clause,[],[f1143,f96,f197,f206])).
% 1.96/0.66  fof(f197,plain,(
% 1.96/0.66    spl5_4 <=> r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0)),
% 1.96/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.96/0.66  fof(f1143,plain,(
% 1.96/0.66    r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl5_1),
% 1.96/0.66    inference(forward_demodulation,[],[f477,f73])).
% 1.96/0.66  fof(f73,plain,(
% 1.96/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.96/0.66    inference(definition_unfolding,[],[f39,f46])).
% 1.96/0.66  fof(f39,plain,(
% 1.96/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.96/0.66    inference(cnf_transformation,[],[f6])).
% 1.96/0.66  fof(f6,axiom,(
% 1.96/0.66    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.96/0.66  fof(f477,plain,(
% 1.96/0.66    r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))) | spl5_1),
% 1.96/0.66    inference(forward_demodulation,[],[f476,f73])).
% 1.96/0.66  fof(f476,plain,(
% 1.96/0.66    r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))) | spl5_1),
% 1.96/0.66    inference(subsumption_resolution,[],[f470,f89])).
% 1.96/0.66  fof(f89,plain,(
% 1.96/0.66    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 1.96/0.66    inference(equality_resolution,[],[f88])).
% 1.96/0.66  fof(f88,plain,(
% 1.96/0.66    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 1.96/0.66    inference(equality_resolution,[],[f81])).
% 1.96/0.66  fof(f81,plain,(
% 1.96/0.66    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.96/0.66    inference(definition_unfolding,[],[f62,f68])).
% 1.96/0.66  fof(f62,plain,(
% 1.96/0.66    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.96/0.66    inference(cnf_transformation,[],[f36])).
% 1.96/0.66  fof(f470,plain,(
% 1.96/0.66    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))) | spl5_1),
% 1.96/0.66    inference(superposition,[],[f168,f74])).
% 1.96/0.66  fof(f74,plain,(
% 1.96/0.66    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 1.96/0.66    inference(definition_unfolding,[],[f40,f67])).
% 1.96/0.66  fof(f67,plain,(
% 1.96/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.96/0.66    inference(definition_unfolding,[],[f45,f46])).
% 1.96/0.66  fof(f45,plain,(
% 1.96/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.96/0.66    inference(cnf_transformation,[],[f8])).
% 1.96/0.66  fof(f8,axiom,(
% 1.96/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.96/0.66  fof(f40,plain,(
% 1.96/0.66    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.96/0.66    inference(cnf_transformation,[],[f5])).
% 1.96/0.66  fof(f5,axiom,(
% 1.96/0.66    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.96/0.66  fof(f168,plain,(
% 1.96/0.66    ( ! [X1] : (~r2_hidden(k5_xboole_0(sK0,X1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X1),X1)) ) | spl5_1),
% 1.96/0.66    inference(superposition,[],[f123,f56])).
% 1.96/0.66  fof(f56,plain,(
% 1.96/0.66    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.96/0.66    inference(cnf_transformation,[],[f31])).
% 1.96/0.66  fof(f31,plain,(
% 1.96/0.66    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.96/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.96/0.66  fof(f30,plain,(
% 1.96/0.66    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.96/0.66    introduced(choice_axiom,[])).
% 1.96/0.66  fof(f29,plain,(
% 1.96/0.66    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.96/0.66    inference(rectify,[],[f28])).
% 1.96/0.66  fof(f28,plain,(
% 1.96/0.66    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.96/0.66    inference(flattening,[],[f27])).
% 1.96/0.66  fof(f27,plain,(
% 1.96/0.66    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.96/0.66    inference(nnf_transformation,[],[f2])).
% 1.96/0.66  fof(f2,axiom,(
% 1.96/0.66    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.96/0.66  fof(f123,plain,(
% 1.96/0.66    ~r2_hidden(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_1),
% 1.96/0.66    inference(unit_resulting_resolution,[],[f98,f98,f98,f94])).
% 1.96/0.66  fof(f94,plain,(
% 1.96/0.66    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.96/0.66    inference(equality_resolution,[],[f84])).
% 1.96/0.66  fof(f84,plain,(
% 1.96/0.66    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.96/0.66    inference(definition_unfolding,[],[f59,f68])).
% 1.96/0.66  fof(f59,plain,(
% 1.96/0.66    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.96/0.66    inference(cnf_transformation,[],[f36])).
% 1.96/0.66  fof(f98,plain,(
% 1.96/0.66    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl5_1),
% 1.96/0.66    inference(avatar_component_clause,[],[f96])).
% 1.96/0.66  fof(f1132,plain,(
% 1.96/0.66    spl5_3 | spl5_4 | spl5_1),
% 1.96/0.66    inference(avatar_split_clause,[],[f1057,f96,f197,f193])).
% 1.96/0.66  fof(f1057,plain,(
% 1.96/0.66    r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),sK0) | spl5_1),
% 1.96/0.66    inference(forward_demodulation,[],[f487,f73])).
% 1.96/0.66  fof(f487,plain,(
% 1.96/0.66    r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),sK0) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))) | spl5_1),
% 1.96/0.66    inference(forward_demodulation,[],[f486,f73])).
% 1.96/0.66  fof(f486,plain,(
% 1.96/0.66    r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),sK0) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))) | spl5_1),
% 1.96/0.66    inference(subsumption_resolution,[],[f480,f89])).
% 1.96/0.66  fof(f480,plain,(
% 1.96/0.66    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),sK0) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0))) | spl5_1),
% 1.96/0.66    inference(superposition,[],[f241,f74])).
% 1.96/0.66  fof(f241,plain,(
% 1.96/0.66    ( ! [X0] : (~r2_hidden(sK0,k3_enumset1(k5_xboole_0(sK0,X0),k5_xboole_0(sK0,X0),k5_xboole_0(sK0,X0),k5_xboole_0(sK0,X0),k5_xboole_0(sK0,X0))) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),sK0) | r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0),X0)) ) | spl5_1),
% 1.96/0.66    inference(superposition,[],[f132,f55])).
% 1.96/0.66  fof(f55,plain,(
% 1.96/0.66    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.96/0.66    inference(cnf_transformation,[],[f31])).
% 1.96/0.66  fof(f132,plain,(
% 1.96/0.66    ~r2_hidden(sK0,k3_enumset1(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))) | spl5_1),
% 1.96/0.66    inference(unit_resulting_resolution,[],[f98,f98,f98,f94])).
% 1.96/0.66  fof(f1130,plain,(
% 1.96/0.66    ~spl5_4),
% 1.96/0.66    inference(avatar_contradiction_clause,[],[f1129])).
% 1.96/0.66  fof(f1129,plain,(
% 1.96/0.66    $false | ~spl5_4),
% 1.96/0.66    inference(subsumption_resolution,[],[f1127,f199])).
% 1.96/0.66  fof(f199,plain,(
% 1.96/0.66    r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0) | ~spl5_4),
% 1.96/0.66    inference(avatar_component_clause,[],[f197])).
% 1.96/0.66  fof(f1127,plain,(
% 1.96/0.66    ~r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0) | ~spl5_4),
% 1.96/0.66    inference(superposition,[],[f367,f73])).
% 1.96/0.66  fof(f367,plain,(
% 1.96/0.66    ( ! [X0] : (~r2_hidden(sK3(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) ) | ~spl5_4),
% 1.96/0.66    inference(unit_resulting_resolution,[],[f75,f199,f49])).
% 1.96/0.66  fof(f104,plain,(
% 1.96/0.66    spl5_1 | ~spl5_2),
% 1.96/0.66    inference(avatar_split_clause,[],[f72,f100,f96])).
% 1.96/0.66  fof(f72,plain,(
% 1.96/0.66    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.96/0.66    inference(definition_unfolding,[],[f37,f46,f70])).
% 1.96/0.66  fof(f37,plain,(
% 1.96/0.66    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.96/0.66    inference(cnf_transformation,[],[f24])).
% 1.96/0.66  fof(f24,plain,(
% 1.96/0.66    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.96/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.96/0.66  fof(f23,plain,(
% 1.96/0.66    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 1.96/0.66    introduced(choice_axiom,[])).
% 1.96/0.66  fof(f22,plain,(
% 1.96/0.66    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.96/0.66    inference(nnf_transformation,[],[f18])).
% 1.96/0.66  fof(f18,plain,(
% 1.96/0.66    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.96/0.66    inference(ennf_transformation,[],[f16])).
% 1.96/0.66  fof(f16,negated_conjecture,(
% 1.96/0.66    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.96/0.66    inference(negated_conjecture,[],[f15])).
% 1.96/0.66  fof(f15,conjecture,(
% 1.96/0.66    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.96/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.96/0.66  fof(f103,plain,(
% 1.96/0.66    ~spl5_1 | spl5_2),
% 1.96/0.66    inference(avatar_split_clause,[],[f71,f100,f96])).
% 1.96/0.66  fof(f71,plain,(
% 1.96/0.66    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.96/0.66    inference(definition_unfolding,[],[f38,f46,f70])).
% 1.96/0.66  fof(f38,plain,(
% 1.96/0.66    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.96/0.66    inference(cnf_transformation,[],[f24])).
% 1.96/0.66  % SZS output end Proof for theBenchmark
% 1.96/0.66  % (31226)------------------------------
% 1.96/0.66  % (31226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.66  % (31226)Termination reason: Refutation
% 1.96/0.66  
% 1.96/0.66  % (31226)Memory used [KB]: 11513
% 1.96/0.66  % (31226)Time elapsed: 0.237 s
% 1.96/0.66  % (31226)------------------------------
% 1.96/0.66  % (31226)------------------------------
% 1.96/0.66  % (31230)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.96/0.66  % (31199)Success in time 0.301 s
%------------------------------------------------------------------------------
