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
% DateTime   : Thu Dec  3 12:43:37 EST 2020

% Result     : Theorem 2.30s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 272 expanded)
%              Number of leaves         :   33 ( 101 expanded)
%              Depth                    :   11
%              Number of atoms          :  369 ( 912 expanded)
%              Number of equality atoms :   53 ( 139 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f87,f91,f95,f100,f108,f120,f130,f709,f733,f866,f876,f882,f1005,f1009,f1093,f1247])).

fof(f1247,plain,
    ( spl6_93
    | ~ spl6_78
    | spl6_79 ),
    inference(avatar_split_clause,[],[f1231,f1007,f1003,f1091])).

fof(f1091,plain,
    ( spl6_93
  <=> r2_hidden(sK4(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f1003,plain,
    ( spl6_78
  <=> r2_hidden(sK4(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1007,plain,
    ( spl6_79
  <=> r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f1231,plain,
    ( r2_hidden(sK4(sK0,sK1),sK1)
    | ~ spl6_78
    | spl6_79 ),
    inference(resolution,[],[f1015,f1008])).

fof(f1008,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl6_79 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f1015,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,X0))
        | r2_hidden(sK4(sK0,sK1),X0) )
    | ~ spl6_78 ),
    inference(resolution,[],[f1004,f77])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1004,plain,
    ( r2_hidden(sK4(sK0,sK1),sK0)
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f1093,plain,
    ( ~ spl6_93
    | ~ spl6_51
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f1088,f880,f731,f1091])).

fof(f731,plain,
    ( spl6_51
  <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f880,plain,
    ( spl6_61
  <=> r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f1088,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),sK1)
    | ~ spl6_51
    | ~ spl6_61 ),
    inference(resolution,[],[f785,f881])).

fof(f881,plain,
    ( r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f880])).

fof(f785,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_51 ),
    inference(superposition,[],[f78,f732])).

fof(f732,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f731])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1009,plain,
    ( ~ spl6_79
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f994,f880,f1007])).

fof(f994,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl6_61 ),
    inference(resolution,[],[f881,f78])).

fof(f1005,plain,
    ( spl6_78
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f993,f880,f1003])).

fof(f993,plain,
    ( r2_hidden(sK4(sK0,sK1),sK0)
    | ~ spl6_61 ),
    inference(resolution,[],[f881,f79])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f882,plain,
    ( spl6_61
    | spl6_60 ),
    inference(avatar_split_clause,[],[f877,f874,f880])).

fof(f874,plain,
    ( spl6_60
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f877,plain,
    ( r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl6_60 ),
    inference(resolution,[],[f875,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f875,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl6_60 ),
    inference(avatar_component_clause,[],[f874])).

fof(f876,plain,
    ( ~ spl6_60
    | spl6_58 ),
    inference(avatar_split_clause,[],[f868,f864,f874])).

fof(f864,plain,
    ( spl6_58
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f868,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl6_58 ),
    inference(resolution,[],[f865,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f865,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_58 ),
    inference(avatar_component_clause,[],[f864])).

fof(f866,plain,
    ( ~ spl6_8
    | ~ spl6_58
    | spl6_5 ),
    inference(avatar_split_clause,[],[f861,f98,f864,f127])).

fof(f127,plain,
    ( spl6_8
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f98,plain,
    ( spl6_5
  <=> r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f861,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2)
    | spl6_5 ),
    inference(resolution,[],[f76,f99])).

fof(f99,plain,
    ( ~ r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f733,plain,
    ( spl6_51
    | ~ spl6_4
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f714,f707,f93,f731])).

fof(f93,plain,
    ( spl6_4
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f707,plain,
    ( spl6_49
  <=> sK1 = k4_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f714,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_4
    | ~ spl6_49 ),
    inference(superposition,[],[f150,f708])).

fof(f708,plain,
    ( sK1 = k4_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f707])).

fof(f150,plain,
    ( ! [X1] : k4_xboole_0(X1,k2_enumset1(sK3,sK3,sK3,sK3)) = k4_xboole_0(k4_xboole_0(X1,k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_4 ),
    inference(resolution,[],[f147,f140])).

fof(f140,plain,(
    ! [X6,X7] : r1_xboole_0(X6,k4_xboole_0(X7,X6)) ),
    inference(trivial_inequality_removal,[],[f138])).

fof(f138,plain,(
    ! [X6,X7] :
      ( X6 != X6
      | r1_xboole_0(X6,k4_xboole_0(X7,X6)) ) ),
    inference(superposition,[],[f50,f115])).

fof(f115,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(resolution,[],[f104,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f104,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X3,X2)
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f49,f48])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0)
        | k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = X0 )
    | ~ spl6_4 ),
    inference(resolution,[],[f146,f104])).

fof(f146,plain,
    ( ! [X0] :
        ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)
        | ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f57,f94])).

fof(f94,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f709,plain,
    ( spl6_49
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f701,f106,f89,f707])).

fof(f89,plain,
    ( spl6_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f106,plain,
    ( spl6_6
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f701,plain,
    ( sK1 = k4_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(resolution,[],[f669,f90])).

fof(f90,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f669,plain,
    ( ! [X27] :
        ( ~ r2_hidden(X27,sK2)
        | sK1 = k4_xboole_0(sK1,k2_enumset1(X27,X27,X27,X27)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f72,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_6 ),
    inference(superposition,[],[f78,f107])).

fof(f107,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f130,plain,
    ( spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f124,f118,f127])).

fof(f118,plain,
    ( spl6_7
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f124,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_7 ),
    inference(superposition,[],[f41,f119])).

fof(f119,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( spl6_7
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f114,f85,f118])).

fof(f85,plain,
    ( spl6_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f114,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f104,f86])).

fof(f86,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f108,plain,
    ( spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f102,f85,f106])).

fof(f102,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f49,f86])).

fof(f100,plain,
    ( ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f96,f81,f98])).

fof(f81,plain,
    ( spl6_1
  <=> r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f96,plain,
    ( ~ r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))
    | spl6_1 ),
    inference(resolution,[],[f48,f82])).

fof(f82,plain,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f95,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f68,f93])).

fof(f68,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f36,f44,f66])).

fof(f36,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f91,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f37,f89])).

fof(f37,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f67,f81])).

fof(f67,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f39,f65])).

fof(f39,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:34:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (18313)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.56  % (18330)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.56  % (18321)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.59/0.57  % (18317)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.59/0.57  % (18316)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.59/0.58  % (18331)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.59/0.58  % (18312)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.59/0.58  % (18323)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.59/0.59  % (18318)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.59/0.59  % (18337)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.59  % (18314)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.59/0.59  % (18315)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.59/0.59  % (18336)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.59/0.60  % (18328)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.59/0.60  % (18320)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.59/0.60  % (18327)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.59/0.61  % (18339)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.59/0.61  % (18329)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.61  % (18333)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.59/0.61  % (18324)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.59/0.61  % (18319)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.59/0.61  % (18334)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.59/0.62  % (18325)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.62  % (18332)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.59/0.62  % (18342)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.59/0.62  % (18341)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.59/0.62  % (18335)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.59/0.63  % (18335)Refutation not found, incomplete strategy% (18335)------------------------------
% 1.59/0.63  % (18335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.63  % (18335)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.63  
% 1.59/0.63  % (18335)Memory used [KB]: 10746
% 1.59/0.63  % (18335)Time elapsed: 0.194 s
% 1.59/0.63  % (18335)------------------------------
% 1.59/0.63  % (18335)------------------------------
% 1.59/0.63  % (18340)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.59/0.63  % (18326)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.59/0.64  % (18338)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.30/0.71  % (18332)Refutation found. Thanks to Tanya!
% 2.30/0.71  % SZS status Theorem for theBenchmark
% 2.30/0.71  % SZS output start Proof for theBenchmark
% 2.30/0.71  fof(f1252,plain,(
% 2.30/0.71    $false),
% 2.30/0.71    inference(avatar_sat_refutation,[],[f83,f87,f91,f95,f100,f108,f120,f130,f709,f733,f866,f876,f882,f1005,f1009,f1093,f1247])).
% 2.30/0.71  fof(f1247,plain,(
% 2.30/0.71    spl6_93 | ~spl6_78 | spl6_79),
% 2.30/0.71    inference(avatar_split_clause,[],[f1231,f1007,f1003,f1091])).
% 2.30/0.71  fof(f1091,plain,(
% 2.30/0.71    spl6_93 <=> r2_hidden(sK4(sK0,sK1),sK1)),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).
% 2.30/0.71  fof(f1003,plain,(
% 2.30/0.71    spl6_78 <=> r2_hidden(sK4(sK0,sK1),sK0)),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 2.30/0.71  fof(f1007,plain,(
% 2.30/0.71    spl6_79 <=> r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 2.30/0.71  fof(f1231,plain,(
% 2.30/0.71    r2_hidden(sK4(sK0,sK1),sK1) | (~spl6_78 | spl6_79)),
% 2.30/0.71    inference(resolution,[],[f1015,f1008])).
% 2.30/0.71  fof(f1008,plain,(
% 2.30/0.71    ~r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,sK1)) | spl6_79),
% 2.30/0.71    inference(avatar_component_clause,[],[f1007])).
% 2.30/0.71  fof(f1015,plain,(
% 2.30/0.71    ( ! [X0] : (r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,X0)) | r2_hidden(sK4(sK0,sK1),X0)) ) | ~spl6_78),
% 2.30/0.71    inference(resolution,[],[f1004,f77])).
% 2.30/0.71  fof(f77,plain,(
% 2.30/0.71    ( ! [X4,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X1) | r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.30/0.71    inference(equality_resolution,[],[f60])).
% 2.30/0.71  fof(f60,plain,(
% 2.30/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.30/0.71    inference(cnf_transformation,[],[f35])).
% 2.30/0.71  fof(f35,plain,(
% 2.30/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 2.30/0.71  fof(f34,plain,(
% 2.30/0.71    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.30/0.71    introduced(choice_axiom,[])).
% 2.30/0.71  fof(f33,plain,(
% 2.30/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.71    inference(rectify,[],[f32])).
% 2.30/0.71  fof(f32,plain,(
% 2.30/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.71    inference(flattening,[],[f31])).
% 2.30/0.71  fof(f31,plain,(
% 2.30/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.71    inference(nnf_transformation,[],[f1])).
% 2.30/0.71  fof(f1,axiom,(
% 2.30/0.71    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.30/0.71  fof(f1004,plain,(
% 2.30/0.71    r2_hidden(sK4(sK0,sK1),sK0) | ~spl6_78),
% 2.30/0.71    inference(avatar_component_clause,[],[f1003])).
% 2.30/0.71  fof(f1093,plain,(
% 2.30/0.71    ~spl6_93 | ~spl6_51 | ~spl6_61),
% 2.30/0.71    inference(avatar_split_clause,[],[f1088,f880,f731,f1091])).
% 2.30/0.71  fof(f731,plain,(
% 2.30/0.71    spl6_51 <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 2.30/0.71  fof(f880,plain,(
% 2.30/0.71    spl6_61 <=> r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 2.30/0.71  fof(f1088,plain,(
% 2.30/0.71    ~r2_hidden(sK4(sK0,sK1),sK1) | (~spl6_51 | ~spl6_61)),
% 2.30/0.71    inference(resolution,[],[f785,f881])).
% 2.30/0.71  fof(f881,plain,(
% 2.30/0.71    r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_61),
% 2.30/0.71    inference(avatar_component_clause,[],[f880])).
% 2.30/0.71  fof(f785,plain,(
% 2.30/0.71    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~r2_hidden(X1,sK1)) ) | ~spl6_51),
% 2.30/0.71    inference(superposition,[],[f78,f732])).
% 2.30/0.71  fof(f732,plain,(
% 2.30/0.71    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl6_51),
% 2.30/0.71    inference(avatar_component_clause,[],[f731])).
% 2.30/0.71  fof(f78,plain,(
% 2.30/0.71    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.30/0.71    inference(equality_resolution,[],[f59])).
% 2.30/0.71  fof(f59,plain,(
% 2.30/0.71    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.30/0.71    inference(cnf_transformation,[],[f35])).
% 2.30/0.71  fof(f1009,plain,(
% 2.30/0.71    ~spl6_79 | ~spl6_61),
% 2.30/0.71    inference(avatar_split_clause,[],[f994,f880,f1007])).
% 2.30/0.71  fof(f994,plain,(
% 2.30/0.71    ~r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl6_61),
% 2.30/0.71    inference(resolution,[],[f881,f78])).
% 2.30/0.71  fof(f1005,plain,(
% 2.30/0.71    spl6_78 | ~spl6_61),
% 2.30/0.71    inference(avatar_split_clause,[],[f993,f880,f1003])).
% 2.30/0.71  fof(f993,plain,(
% 2.30/0.71    r2_hidden(sK4(sK0,sK1),sK0) | ~spl6_61),
% 2.30/0.71    inference(resolution,[],[f881,f79])).
% 2.30/0.71  fof(f79,plain,(
% 2.30/0.71    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 2.30/0.71    inference(equality_resolution,[],[f58])).
% 2.30/0.71  fof(f58,plain,(
% 2.30/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.30/0.71    inference(cnf_transformation,[],[f35])).
% 2.30/0.71  fof(f882,plain,(
% 2.30/0.71    spl6_61 | spl6_60),
% 2.30/0.71    inference(avatar_split_clause,[],[f877,f874,f880])).
% 2.30/0.71  fof(f874,plain,(
% 2.30/0.71    spl6_60 <=> r1_xboole_0(sK0,sK1)),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 2.30/0.71  fof(f877,plain,(
% 2.30/0.71    r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl6_60),
% 2.30/0.71    inference(resolution,[],[f875,f71])).
% 2.30/0.71  fof(f71,plain,(
% 2.30/0.71    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.30/0.71    inference(definition_unfolding,[],[f46,f44])).
% 2.30/0.71  fof(f44,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.30/0.71    inference(cnf_transformation,[],[f5])).
% 2.30/0.71  fof(f5,axiom,(
% 2.30/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.30/0.71  fof(f46,plain,(
% 2.30/0.71    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f28])).
% 2.30/0.71  fof(f28,plain,(
% 2.30/0.71    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.30/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f27])).
% 2.30/0.71  fof(f27,plain,(
% 2.30/0.71    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.30/0.71    introduced(choice_axiom,[])).
% 2.30/0.71  fof(f20,plain,(
% 2.30/0.71    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.30/0.71    inference(ennf_transformation,[],[f17])).
% 2.30/0.71  fof(f17,plain,(
% 2.30/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.30/0.71    inference(rectify,[],[f3])).
% 2.30/0.71  fof(f3,axiom,(
% 2.30/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.30/0.71  fof(f875,plain,(
% 2.30/0.71    ~r1_xboole_0(sK0,sK1) | spl6_60),
% 2.30/0.71    inference(avatar_component_clause,[],[f874])).
% 2.30/0.71  fof(f876,plain,(
% 2.30/0.71    ~spl6_60 | spl6_58),
% 2.30/0.71    inference(avatar_split_clause,[],[f868,f864,f874])).
% 2.30/0.71  fof(f864,plain,(
% 2.30/0.71    spl6_58 <=> r1_xboole_0(sK1,sK0)),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 2.30/0.71  fof(f868,plain,(
% 2.30/0.71    ~r1_xboole_0(sK0,sK1) | spl6_58),
% 2.30/0.71    inference(resolution,[],[f865,f48])).
% 2.30/0.71  fof(f48,plain,(
% 2.30/0.71    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f21])).
% 2.30/0.71  fof(f21,plain,(
% 2.30/0.71    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.30/0.71    inference(ennf_transformation,[],[f2])).
% 2.30/0.71  fof(f2,axiom,(
% 2.30/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.30/0.71  fof(f865,plain,(
% 2.30/0.71    ~r1_xboole_0(sK1,sK0) | spl6_58),
% 2.30/0.71    inference(avatar_component_clause,[],[f864])).
% 2.30/0.71  fof(f866,plain,(
% 2.30/0.71    ~spl6_8 | ~spl6_58 | spl6_5),
% 2.30/0.71    inference(avatar_split_clause,[],[f861,f98,f864,f127])).
% 2.30/0.71  fof(f127,plain,(
% 2.30/0.71    spl6_8 <=> r1_xboole_0(sK1,sK2)),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.30/0.71  fof(f98,plain,(
% 2.30/0.71    spl6_5 <=> r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.30/0.71  fof(f861,plain,(
% 2.30/0.71    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2) | spl6_5),
% 2.30/0.71    inference(resolution,[],[f76,f99])).
% 2.30/0.71  fof(f99,plain,(
% 2.30/0.71    ~r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))) | spl6_5),
% 2.30/0.71    inference(avatar_component_clause,[],[f98])).
% 2.30/0.71  fof(f76,plain,(
% 2.30/0.71    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 2.30/0.71    inference(definition_unfolding,[],[f54,f65])).
% 2.30/0.71  fof(f65,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.30/0.71    inference(definition_unfolding,[],[f42,f64])).
% 2.30/0.71  fof(f64,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.30/0.71    inference(definition_unfolding,[],[f43,f53])).
% 2.30/0.71  fof(f53,plain,(
% 2.30/0.71    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f12])).
% 2.30/0.71  fof(f12,axiom,(
% 2.30/0.71    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.30/0.71  fof(f43,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f11])).
% 2.30/0.71  fof(f11,axiom,(
% 2.30/0.71    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.30/0.71  fof(f42,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f13])).
% 2.30/0.71  fof(f13,axiom,(
% 2.30/0.71    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.30/0.71  fof(f54,plain,(
% 2.30/0.71    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.30/0.71    inference(cnf_transformation,[],[f22])).
% 2.30/0.71  fof(f22,plain,(
% 2.30/0.71    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.30/0.71    inference(ennf_transformation,[],[f7])).
% 2.30/0.71  fof(f7,axiom,(
% 2.30/0.71    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.30/0.71  fof(f733,plain,(
% 2.30/0.71    spl6_51 | ~spl6_4 | ~spl6_49),
% 2.30/0.71    inference(avatar_split_clause,[],[f714,f707,f93,f731])).
% 2.30/0.71  fof(f93,plain,(
% 2.30/0.71    spl6_4 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.30/0.71  fof(f707,plain,(
% 2.30/0.71    spl6_49 <=> sK1 = k4_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 2.30/0.71  fof(f714,plain,(
% 2.30/0.71    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl6_4 | ~spl6_49)),
% 2.30/0.71    inference(superposition,[],[f150,f708])).
% 2.30/0.71  fof(f708,plain,(
% 2.30/0.71    sK1 = k4_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl6_49),
% 2.30/0.71    inference(avatar_component_clause,[],[f707])).
% 2.30/0.71  fof(f150,plain,(
% 2.30/0.71    ( ! [X1] : (k4_xboole_0(X1,k2_enumset1(sK3,sK3,sK3,sK3)) = k4_xboole_0(k4_xboole_0(X1,k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl6_4),
% 2.30/0.71    inference(resolution,[],[f147,f140])).
% 2.30/0.71  fof(f140,plain,(
% 2.30/0.71    ( ! [X6,X7] : (r1_xboole_0(X6,k4_xboole_0(X7,X6))) )),
% 2.30/0.71    inference(trivial_inequality_removal,[],[f138])).
% 2.30/0.71  fof(f138,plain,(
% 2.30/0.71    ( ! [X6,X7] : (X6 != X6 | r1_xboole_0(X6,k4_xboole_0(X7,X6))) )),
% 2.30/0.71    inference(superposition,[],[f50,f115])).
% 2.30/0.71  fof(f115,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 2.30/0.71    inference(resolution,[],[f104,f41])).
% 2.30/0.71  fof(f41,plain,(
% 2.30/0.71    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f8])).
% 2.30/0.71  fof(f8,axiom,(
% 2.30/0.71    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.30/0.71  fof(f104,plain,(
% 2.30/0.71    ( ! [X2,X3] : (~r1_xboole_0(X3,X2) | k4_xboole_0(X2,X3) = X2) )),
% 2.30/0.71    inference(resolution,[],[f49,f48])).
% 2.30/0.71  fof(f49,plain,(
% 2.30/0.71    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.30/0.71    inference(cnf_transformation,[],[f29])).
% 2.30/0.71  fof(f29,plain,(
% 2.30/0.71    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.30/0.71    inference(nnf_transformation,[],[f9])).
% 2.30/0.71  fof(f9,axiom,(
% 2.30/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.30/0.71  fof(f50,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f29])).
% 2.30/0.71  fof(f147,plain,(
% 2.30/0.71    ( ! [X0] : (~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0) | k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = X0) ) | ~spl6_4),
% 2.30/0.71    inference(resolution,[],[f146,f104])).
% 2.30/0.71  fof(f146,plain,(
% 2.30/0.71    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) | ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0)) ) | ~spl6_4),
% 2.30/0.71    inference(resolution,[],[f57,f94])).
% 2.30/0.71  fof(f94,plain,(
% 2.30/0.71    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl6_4),
% 2.30/0.71    inference(avatar_component_clause,[],[f93])).
% 2.30/0.71  fof(f57,plain,(
% 2.30/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f24])).
% 2.30/0.71  fof(f24,plain,(
% 2.30/0.71    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.30/0.71    inference(flattening,[],[f23])).
% 2.30/0.71  fof(f23,plain,(
% 2.30/0.71    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.30/0.71    inference(ennf_transformation,[],[f6])).
% 2.30/0.71  fof(f6,axiom,(
% 2.30/0.71    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.30/0.71  fof(f709,plain,(
% 2.30/0.71    spl6_49 | ~spl6_3 | ~spl6_6),
% 2.30/0.71    inference(avatar_split_clause,[],[f701,f106,f89,f707])).
% 2.30/0.71  fof(f89,plain,(
% 2.30/0.71    spl6_3 <=> r2_hidden(sK3,sK2)),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.30/0.71  fof(f106,plain,(
% 2.30/0.71    spl6_6 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.30/0.71  fof(f701,plain,(
% 2.30/0.71    sK1 = k4_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | (~spl6_3 | ~spl6_6)),
% 2.30/0.71    inference(resolution,[],[f669,f90])).
% 2.30/0.71  fof(f90,plain,(
% 2.30/0.71    r2_hidden(sK3,sK2) | ~spl6_3),
% 2.30/0.71    inference(avatar_component_clause,[],[f89])).
% 2.30/0.71  fof(f669,plain,(
% 2.30/0.71    ( ! [X27] : (~r2_hidden(X27,sK2) | sK1 = k4_xboole_0(sK1,k2_enumset1(X27,X27,X27,X27))) ) | ~spl6_6),
% 2.30/0.71    inference(resolution,[],[f72,f112])).
% 2.30/0.71  fof(f112,plain,(
% 2.30/0.71    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2)) ) | ~spl6_6),
% 2.30/0.71    inference(superposition,[],[f78,f107])).
% 2.30/0.71  fof(f107,plain,(
% 2.30/0.71    sK2 = k4_xboole_0(sK2,sK1) | ~spl6_6),
% 2.30/0.71    inference(avatar_component_clause,[],[f106])).
% 2.30/0.71  fof(f72,plain,(
% 2.30/0.71    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 2.30/0.71    inference(definition_unfolding,[],[f52,f66])).
% 2.30/0.71  fof(f66,plain,(
% 2.30/0.71    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.30/0.71    inference(definition_unfolding,[],[f40,f64])).
% 2.30/0.71  fof(f40,plain,(
% 2.30/0.71    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f10])).
% 2.30/0.71  fof(f10,axiom,(
% 2.30/0.71    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.30/0.71  fof(f52,plain,(
% 2.30/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.30/0.71    inference(cnf_transformation,[],[f30])).
% 2.30/0.71  fof(f30,plain,(
% 2.30/0.71    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.30/0.71    inference(nnf_transformation,[],[f14])).
% 2.30/0.71  fof(f14,axiom,(
% 2.30/0.71    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.30/0.71  fof(f130,plain,(
% 2.30/0.71    spl6_8 | ~spl6_7),
% 2.30/0.71    inference(avatar_split_clause,[],[f124,f118,f127])).
% 2.30/0.71  fof(f118,plain,(
% 2.30/0.71    spl6_7 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.30/0.71  fof(f124,plain,(
% 2.30/0.71    r1_xboole_0(sK1,sK2) | ~spl6_7),
% 2.30/0.71    inference(superposition,[],[f41,f119])).
% 2.30/0.71  fof(f119,plain,(
% 2.30/0.71    sK1 = k4_xboole_0(sK1,sK2) | ~spl6_7),
% 2.30/0.71    inference(avatar_component_clause,[],[f118])).
% 2.30/0.71  fof(f120,plain,(
% 2.30/0.71    spl6_7 | ~spl6_2),
% 2.30/0.71    inference(avatar_split_clause,[],[f114,f85,f118])).
% 2.30/0.71  fof(f85,plain,(
% 2.30/0.71    spl6_2 <=> r1_xboole_0(sK2,sK1)),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.30/0.71  fof(f114,plain,(
% 2.30/0.71    sK1 = k4_xboole_0(sK1,sK2) | ~spl6_2),
% 2.30/0.71    inference(resolution,[],[f104,f86])).
% 2.30/0.71  fof(f86,plain,(
% 2.30/0.71    r1_xboole_0(sK2,sK1) | ~spl6_2),
% 2.30/0.71    inference(avatar_component_clause,[],[f85])).
% 2.30/0.71  fof(f108,plain,(
% 2.30/0.71    spl6_6 | ~spl6_2),
% 2.30/0.71    inference(avatar_split_clause,[],[f102,f85,f106])).
% 2.30/0.71  fof(f102,plain,(
% 2.30/0.71    sK2 = k4_xboole_0(sK2,sK1) | ~spl6_2),
% 2.30/0.71    inference(resolution,[],[f49,f86])).
% 2.30/0.71  fof(f100,plain,(
% 2.30/0.71    ~spl6_5 | spl6_1),
% 2.30/0.71    inference(avatar_split_clause,[],[f96,f81,f98])).
% 2.30/0.71  fof(f81,plain,(
% 2.30/0.71    spl6_1 <=> r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 2.30/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.30/0.71  fof(f96,plain,(
% 2.30/0.71    ~r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))) | spl6_1),
% 2.30/0.71    inference(resolution,[],[f48,f82])).
% 2.30/0.71  fof(f82,plain,(
% 2.30/0.71    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) | spl6_1),
% 2.30/0.71    inference(avatar_component_clause,[],[f81])).
% 2.30/0.71  fof(f95,plain,(
% 2.30/0.71    spl6_4),
% 2.30/0.71    inference(avatar_split_clause,[],[f68,f93])).
% 2.30/0.71  fof(f68,plain,(
% 2.30/0.71    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 2.30/0.71    inference(definition_unfolding,[],[f36,f44,f66])).
% 2.30/0.71  fof(f36,plain,(
% 2.30/0.71    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.30/0.71    inference(cnf_transformation,[],[f26])).
% 2.30/0.71  fof(f26,plain,(
% 2.30/0.71    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.30/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f25])).
% 2.30/0.71  fof(f25,plain,(
% 2.30/0.71    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 2.30/0.71    introduced(choice_axiom,[])).
% 2.30/0.71  fof(f19,plain,(
% 2.30/0.71    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 2.30/0.71    inference(flattening,[],[f18])).
% 2.30/0.71  fof(f18,plain,(
% 2.30/0.71    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 2.30/0.71    inference(ennf_transformation,[],[f16])).
% 2.30/0.71  fof(f16,negated_conjecture,(
% 2.30/0.71    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.30/0.71    inference(negated_conjecture,[],[f15])).
% 2.30/0.71  fof(f15,conjecture,(
% 2.30/0.71    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.30/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 2.30/0.71  fof(f91,plain,(
% 2.30/0.71    spl6_3),
% 2.30/0.71    inference(avatar_split_clause,[],[f37,f89])).
% 2.30/0.71  fof(f37,plain,(
% 2.30/0.71    r2_hidden(sK3,sK2)),
% 2.30/0.71    inference(cnf_transformation,[],[f26])).
% 2.30/0.71  fof(f87,plain,(
% 2.30/0.71    spl6_2),
% 2.30/0.71    inference(avatar_split_clause,[],[f38,f85])).
% 2.30/0.71  fof(f38,plain,(
% 2.30/0.71    r1_xboole_0(sK2,sK1)),
% 2.30/0.71    inference(cnf_transformation,[],[f26])).
% 2.30/0.71  fof(f83,plain,(
% 2.30/0.71    ~spl6_1),
% 2.30/0.71    inference(avatar_split_clause,[],[f67,f81])).
% 2.30/0.71  fof(f67,plain,(
% 2.30/0.71    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 2.30/0.71    inference(definition_unfolding,[],[f39,f65])).
% 2.30/0.71  fof(f39,plain,(
% 2.30/0.71    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 2.30/0.71    inference(cnf_transformation,[],[f26])).
% 2.30/0.71  % SZS output end Proof for theBenchmark
% 2.30/0.71  % (18332)------------------------------
% 2.30/0.71  % (18332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.71  % (18332)Termination reason: Refutation
% 2.30/0.71  
% 2.30/0.71  % (18332)Memory used [KB]: 11641
% 2.30/0.71  % (18332)Time elapsed: 0.257 s
% 2.30/0.71  % (18332)------------------------------
% 2.30/0.71  % (18332)------------------------------
% 2.30/0.72  % (18311)Success in time 0.352 s
%------------------------------------------------------------------------------
