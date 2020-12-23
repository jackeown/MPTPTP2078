%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:59 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 194 expanded)
%              Number of leaves         :   23 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  291 ( 836 expanded)
%              Number of equality atoms :   39 ( 103 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f758,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f82,f87,f95,f121,f147,f380,f503,f615,f757])).

fof(f757,plain,
    ( spl5_4
    | ~ spl5_8
    | spl5_33 ),
    inference(avatar_contradiction_clause,[],[f756])).

fof(f756,plain,
    ( $false
    | spl5_4
    | ~ spl5_8
    | spl5_33 ),
    inference(subsumption_resolution,[],[f755,f106])).

fof(f106,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK1,X0))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f81,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f81,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_4
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f755,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK1,sK2))
    | ~ spl5_8
    | spl5_33 ),
    inference(forward_demodulation,[],[f714,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f714,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_xboole_0(k2_xboole_0(sK1,sK2),sK2))
    | ~ spl5_8
    | spl5_33 ),
    inference(unit_resulting_resolution,[],[f120,f613,f56])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f613,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK2)
    | spl5_33 ),
    inference(avatar_component_clause,[],[f611])).

fof(f611,plain,
    ( spl5_33
  <=> r2_hidden(sK3(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f120,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_8
  <=> r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f615,plain,
    ( ~ spl5_33
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f581,f419,f611])).

fof(f419,plain,
    ( spl5_24
  <=> r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f581,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK2)
    | ~ spl5_24 ),
    inference(resolution,[],[f421,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f421,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f419])).

fof(f503,plain,
    ( spl5_24
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f471,f377,f91,f84,f419])).

fof(f84,plain,
    ( spl5_5
  <=> r2_hidden(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f91,plain,
    ( spl5_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f377,plain,
    ( spl5_21
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f471,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f86,f408,f139])).

fof(f139,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | r2_hidden(X4,k4_xboole_0(sK0,sK2))
        | r2_hidden(X4,k1_xboole_0) )
    | ~ spl5_6 ),
    inference(superposition,[],[f56,f93])).

fof(f93,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f408,plain,
    ( ! [X5] : ~ r2_hidden(X5,k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f396,f141])).

fof(f141,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k1_xboole_0)
        | r2_hidden(X6,sK0) )
    | ~ spl5_6 ),
    inference(superposition,[],[f58,f93])).

fof(f396,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_xboole_0)
        | ~ r2_hidden(X5,sK0) )
    | ~ spl5_21 ),
    inference(superposition,[],[f57,f379])).

fof(f379,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f377])).

fof(f86,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f380,plain,
    ( spl5_21
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f375,f144,f91,f377])).

fof(f144,plain,
    ( spl5_10
  <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f375,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f357,f93])).

fof(f357,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(superposition,[],[f134,f146])).

fof(f146,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f134,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl5_6 ),
    inference(superposition,[],[f47,f93])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f147,plain,
    ( spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f142,f91,f144])).

fof(f142,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f133,f35])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f133,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl5_6 ),
    inference(superposition,[],[f40,f93])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f121,plain,
    ( spl5_8
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f112,f84,f70,f118])).

fof(f70,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f112,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f72,f86,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f95,plain,
    ( spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f89,f65,f91])).

fof(f65,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f89,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f67,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f67,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f87,plain,
    ( spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f74,f60,f84])).

fof(f60,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f74,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f62,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f82,plain,
    ( ~ spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f75,f60,f79])).

fof(f75,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f62,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f68,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f33,f65])).

fof(f33,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f34,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (30456)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (30450)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (30441)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (30458)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (30458)Refutation not found, incomplete strategy% (30458)------------------------------
% 0.21/0.51  % (30458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30443)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (30458)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30458)Memory used [KB]: 10618
% 0.21/0.51  % (30458)Time elapsed: 0.055 s
% 0.21/0.51  % (30458)------------------------------
% 0.21/0.51  % (30458)------------------------------
% 0.21/0.51  % (30438)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.16/0.51  % (30440)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.16/0.51  % (30464)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.16/0.52  % (30442)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.16/0.53  % (30439)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.53  % (30453)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.53  % (30455)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.53  % (30453)Refutation not found, incomplete strategy% (30453)------------------------------
% 1.34/0.53  % (30453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (30453)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (30453)Memory used [KB]: 10618
% 1.34/0.53  % (30453)Time elapsed: 0.132 s
% 1.34/0.53  % (30453)------------------------------
% 1.34/0.53  % (30453)------------------------------
% 1.34/0.54  % (30449)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.54  % (30437)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.54  % (30463)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.54  % (30466)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.54  % (30461)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.54  % (30465)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.55  % (30459)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.55  % (30454)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.55  % (30452)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.55  % (30446)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.55  % (30457)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.55  % (30448)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.55  % (30451)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.55  % (30445)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.55  % (30436)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.56  % (30460)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.56  % (30447)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.56  % (30447)Refutation not found, incomplete strategy% (30447)------------------------------
% 1.34/0.56  % (30447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (30447)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (30447)Memory used [KB]: 10618
% 1.34/0.56  % (30447)Time elapsed: 0.161 s
% 1.34/0.56  % (30447)------------------------------
% 1.34/0.56  % (30447)------------------------------
% 1.34/0.56  % (30444)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.57  % (30461)Refutation found. Thanks to Tanya!
% 1.34/0.57  % SZS status Theorem for theBenchmark
% 1.34/0.57  % SZS output start Proof for theBenchmark
% 1.34/0.57  fof(f758,plain,(
% 1.34/0.57    $false),
% 1.34/0.57    inference(avatar_sat_refutation,[],[f63,f68,f73,f82,f87,f95,f121,f147,f380,f503,f615,f757])).
% 1.34/0.57  fof(f757,plain,(
% 1.34/0.57    spl5_4 | ~spl5_8 | spl5_33),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f756])).
% 1.34/0.57  fof(f756,plain,(
% 1.34/0.57    $false | (spl5_4 | ~spl5_8 | spl5_33)),
% 1.34/0.57    inference(subsumption_resolution,[],[f755,f106])).
% 1.34/0.57  fof(f106,plain,(
% 1.34/0.57    ( ! [X0] : (~r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK1,X0))) ) | spl5_4),
% 1.34/0.57    inference(unit_resulting_resolution,[],[f81,f58])).
% 1.34/0.57  fof(f58,plain,(
% 1.34/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.34/0.57    inference(equality_resolution,[],[f48])).
% 1.34/0.57  fof(f48,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.34/0.57    inference(cnf_transformation,[],[f31])).
% 1.34/0.57  fof(f31,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 1.34/0.57  fof(f30,plain,(
% 1.34/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.34/0.57    introduced(choice_axiom,[])).
% 1.34/0.57  fof(f29,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.57    inference(rectify,[],[f28])).
% 1.34/0.57  fof(f28,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.57    inference(flattening,[],[f27])).
% 1.34/0.57  fof(f27,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.57    inference(nnf_transformation,[],[f4])).
% 1.34/0.57  fof(f4,axiom,(
% 1.34/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.34/0.57  fof(f81,plain,(
% 1.34/0.57    ~r2_hidden(sK3(sK0,sK1),sK1) | spl5_4),
% 1.34/0.57    inference(avatar_component_clause,[],[f79])).
% 1.34/0.57  fof(f79,plain,(
% 1.34/0.57    spl5_4 <=> r2_hidden(sK3(sK0,sK1),sK1)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.34/0.57  fof(f755,plain,(
% 1.34/0.57    r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK1,sK2)) | (~spl5_8 | spl5_33)),
% 1.34/0.57    inference(forward_demodulation,[],[f714,f41])).
% 1.34/0.57  fof(f41,plain,(
% 1.34/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f10])).
% 1.34/0.57  fof(f10,axiom,(
% 1.34/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.34/0.57  fof(f714,plain,(
% 1.34/0.57    r2_hidden(sK3(sK0,sK1),k4_xboole_0(k2_xboole_0(sK1,sK2),sK2)) | (~spl5_8 | spl5_33)),
% 1.34/0.57    inference(unit_resulting_resolution,[],[f120,f613,f56])).
% 1.34/0.57  fof(f56,plain,(
% 1.34/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.34/0.57    inference(equality_resolution,[],[f50])).
% 1.34/0.57  fof(f50,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.34/0.57    inference(cnf_transformation,[],[f31])).
% 1.34/0.57  fof(f613,plain,(
% 1.34/0.57    ~r2_hidden(sK3(sK0,sK1),sK2) | spl5_33),
% 1.34/0.57    inference(avatar_component_clause,[],[f611])).
% 1.34/0.57  fof(f611,plain,(
% 1.34/0.57    spl5_33 <=> r2_hidden(sK3(sK0,sK1),sK2)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.34/0.57  fof(f120,plain,(
% 1.34/0.57    r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2)) | ~spl5_8),
% 1.34/0.57    inference(avatar_component_clause,[],[f118])).
% 1.34/0.57  fof(f118,plain,(
% 1.34/0.57    spl5_8 <=> r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.34/0.57  fof(f615,plain,(
% 1.34/0.57    ~spl5_33 | ~spl5_24),
% 1.34/0.57    inference(avatar_split_clause,[],[f581,f419,f611])).
% 1.34/0.57  fof(f419,plain,(
% 1.34/0.57    spl5_24 <=> r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.34/0.57  fof(f581,plain,(
% 1.34/0.57    ~r2_hidden(sK3(sK0,sK1),sK2) | ~spl5_24),
% 1.34/0.57    inference(resolution,[],[f421,f57])).
% 1.34/0.57  fof(f57,plain,(
% 1.34/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.34/0.57    inference(equality_resolution,[],[f49])).
% 1.34/0.57  fof(f49,plain,(
% 1.34/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.34/0.57    inference(cnf_transformation,[],[f31])).
% 1.34/0.57  fof(f421,plain,(
% 1.34/0.57    r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2)) | ~spl5_24),
% 1.34/0.57    inference(avatar_component_clause,[],[f419])).
% 1.34/0.57  fof(f503,plain,(
% 1.34/0.57    spl5_24 | ~spl5_5 | ~spl5_6 | ~spl5_21),
% 1.34/0.57    inference(avatar_split_clause,[],[f471,f377,f91,f84,f419])).
% 1.34/0.57  fof(f84,plain,(
% 1.34/0.57    spl5_5 <=> r2_hidden(sK3(sK0,sK1),sK0)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.34/0.57  fof(f91,plain,(
% 1.34/0.57    spl5_6 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.34/0.57  fof(f377,plain,(
% 1.34/0.57    spl5_21 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.34/0.57  fof(f471,plain,(
% 1.34/0.57    r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2)) | (~spl5_5 | ~spl5_6 | ~spl5_21)),
% 1.34/0.57    inference(unit_resulting_resolution,[],[f86,f408,f139])).
% 1.34/0.57  fof(f139,plain,(
% 1.34/0.57    ( ! [X4] : (~r2_hidden(X4,sK0) | r2_hidden(X4,k4_xboole_0(sK0,sK2)) | r2_hidden(X4,k1_xboole_0)) ) | ~spl5_6),
% 1.34/0.57    inference(superposition,[],[f56,f93])).
% 1.34/0.57  fof(f93,plain,(
% 1.34/0.57    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_6),
% 1.34/0.57    inference(avatar_component_clause,[],[f91])).
% 1.34/0.57  fof(f408,plain,(
% 1.34/0.57    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) ) | (~spl5_6 | ~spl5_21)),
% 1.34/0.57    inference(subsumption_resolution,[],[f396,f141])).
% 1.34/0.57  fof(f141,plain,(
% 1.34/0.57    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | r2_hidden(X6,sK0)) ) | ~spl5_6),
% 1.34/0.57    inference(superposition,[],[f58,f93])).
% 1.34/0.57  fof(f396,plain,(
% 1.34/0.57    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X5,sK0)) ) | ~spl5_21),
% 1.34/0.57    inference(superposition,[],[f57,f379])).
% 1.34/0.57  fof(f379,plain,(
% 1.34/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) | ~spl5_21),
% 1.34/0.57    inference(avatar_component_clause,[],[f377])).
% 1.34/0.57  fof(f86,plain,(
% 1.34/0.57    r2_hidden(sK3(sK0,sK1),sK0) | ~spl5_5),
% 1.34/0.57    inference(avatar_component_clause,[],[f84])).
% 1.34/0.57  fof(f380,plain,(
% 1.34/0.57    spl5_21 | ~spl5_6 | ~spl5_10),
% 1.34/0.57    inference(avatar_split_clause,[],[f375,f144,f91,f377])).
% 1.34/0.57  fof(f144,plain,(
% 1.34/0.57    spl5_10 <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.34/0.57  fof(f375,plain,(
% 1.34/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) | (~spl5_6 | ~spl5_10)),
% 1.34/0.57    inference(forward_demodulation,[],[f357,f93])).
% 1.34/0.57  fof(f357,plain,(
% 1.34/0.57    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(k1_xboole_0,sK0) | (~spl5_6 | ~spl5_10)),
% 1.34/0.57    inference(superposition,[],[f134,f146])).
% 1.34/0.57  fof(f146,plain,(
% 1.34/0.57    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) | ~spl5_10),
% 1.34/0.57    inference(avatar_component_clause,[],[f144])).
% 1.34/0.57  fof(f134,plain,(
% 1.34/0.57    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl5_6),
% 1.34/0.57    inference(superposition,[],[f47,f93])).
% 1.34/0.57  fof(f47,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.34/0.57    inference(cnf_transformation,[],[f11])).
% 1.34/0.57  fof(f11,axiom,(
% 1.34/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.34/0.57  fof(f147,plain,(
% 1.34/0.57    spl5_10 | ~spl5_6),
% 1.34/0.57    inference(avatar_split_clause,[],[f142,f91,f144])).
% 1.34/0.57  fof(f142,plain,(
% 1.34/0.57    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) | ~spl5_6),
% 1.34/0.57    inference(forward_demodulation,[],[f133,f35])).
% 1.34/0.57  fof(f35,plain,(
% 1.34/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.34/0.57    inference(cnf_transformation,[],[f7])).
% 1.34/0.57  fof(f7,axiom,(
% 1.34/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.34/0.57  fof(f133,plain,(
% 1.34/0.57    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) | ~spl5_6),
% 1.34/0.57    inference(superposition,[],[f40,f93])).
% 1.34/0.57  fof(f40,plain,(
% 1.34/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.34/0.57    inference(cnf_transformation,[],[f8])).
% 1.34/0.57  fof(f8,axiom,(
% 1.34/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.34/0.57  fof(f121,plain,(
% 1.34/0.57    spl5_8 | ~spl5_3 | ~spl5_5),
% 1.34/0.57    inference(avatar_split_clause,[],[f112,f84,f70,f118])).
% 1.34/0.57  fof(f70,plain,(
% 1.34/0.57    spl5_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.34/0.57  fof(f112,plain,(
% 1.34/0.57    r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2)) | (~spl5_3 | ~spl5_5)),
% 1.34/0.57    inference(unit_resulting_resolution,[],[f72,f86,f44])).
% 1.34/0.57  fof(f44,plain,(
% 1.34/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f26])).
% 1.34/0.57  fof(f26,plain,(
% 1.34/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 1.34/0.57  fof(f25,plain,(
% 1.34/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.34/0.57    introduced(choice_axiom,[])).
% 1.34/0.57  fof(f24,plain,(
% 1.34/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.57    inference(rectify,[],[f23])).
% 1.34/0.57  fof(f23,plain,(
% 1.34/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.57    inference(nnf_transformation,[],[f20])).
% 1.34/0.57  fof(f20,plain,(
% 1.34/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f3])).
% 1.34/0.57  fof(f3,axiom,(
% 1.34/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.57  fof(f72,plain,(
% 1.34/0.57    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_3),
% 1.34/0.57    inference(avatar_component_clause,[],[f70])).
% 1.34/0.57  fof(f95,plain,(
% 1.34/0.57    spl5_6 | ~spl5_2),
% 1.34/0.57    inference(avatar_split_clause,[],[f89,f65,f91])).
% 1.34/0.57  fof(f65,plain,(
% 1.34/0.57    spl5_2 <=> r1_xboole_0(sK0,sK2)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.34/0.57  fof(f89,plain,(
% 1.34/0.57    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_2),
% 1.34/0.57    inference(resolution,[],[f67,f55])).
% 1.34/0.57  fof(f55,plain,(
% 1.34/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.34/0.57    inference(definition_unfolding,[],[f43,f39])).
% 1.34/0.57  fof(f39,plain,(
% 1.34/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.34/0.57    inference(cnf_transformation,[],[f12])).
% 1.34/0.57  fof(f12,axiom,(
% 1.34/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.34/0.57  fof(f43,plain,(
% 1.34/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f19])).
% 1.34/0.57  fof(f19,plain,(
% 1.34/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 1.34/0.57    inference(ennf_transformation,[],[f15])).
% 1.34/0.57  fof(f15,plain,(
% 1.34/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.34/0.57    inference(unused_predicate_definition_removal,[],[f5])).
% 1.34/0.57  fof(f5,axiom,(
% 1.34/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.34/0.57  fof(f67,plain,(
% 1.34/0.57    r1_xboole_0(sK0,sK2) | ~spl5_2),
% 1.34/0.57    inference(avatar_component_clause,[],[f65])).
% 1.34/0.57  fof(f87,plain,(
% 1.34/0.57    spl5_5 | spl5_1),
% 1.34/0.57    inference(avatar_split_clause,[],[f74,f60,f84])).
% 1.34/0.57  fof(f60,plain,(
% 1.34/0.57    spl5_1 <=> r1_tarski(sK0,sK1)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.34/0.57  fof(f74,plain,(
% 1.34/0.57    r2_hidden(sK3(sK0,sK1),sK0) | spl5_1),
% 1.34/0.57    inference(unit_resulting_resolution,[],[f62,f45])).
% 1.34/0.57  fof(f45,plain,(
% 1.34/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f26])).
% 1.34/0.57  fof(f62,plain,(
% 1.34/0.57    ~r1_tarski(sK0,sK1) | spl5_1),
% 1.34/0.57    inference(avatar_component_clause,[],[f60])).
% 1.34/0.57  fof(f82,plain,(
% 1.34/0.57    ~spl5_4 | spl5_1),
% 1.34/0.57    inference(avatar_split_clause,[],[f75,f60,f79])).
% 1.34/0.57  fof(f75,plain,(
% 1.34/0.57    ~r2_hidden(sK3(sK0,sK1),sK1) | spl5_1),
% 1.34/0.57    inference(unit_resulting_resolution,[],[f62,f46])).
% 1.34/0.57  fof(f46,plain,(
% 1.34/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f26])).
% 1.34/0.57  fof(f73,plain,(
% 1.34/0.57    spl5_3),
% 1.34/0.57    inference(avatar_split_clause,[],[f32,f70])).
% 1.34/0.57  fof(f32,plain,(
% 1.34/0.57    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.34/0.57    inference(cnf_transformation,[],[f22])).
% 1.34/0.57  fof(f22,plain,(
% 1.34/0.57    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.34/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21])).
% 1.34/0.57  fof(f21,plain,(
% 1.34/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 1.34/0.57    introduced(choice_axiom,[])).
% 1.34/0.57  fof(f17,plain,(
% 1.34/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.34/0.57    inference(flattening,[],[f16])).
% 1.34/0.57  fof(f16,plain,(
% 1.34/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.34/0.57    inference(ennf_transformation,[],[f14])).
% 1.34/0.57  fof(f14,negated_conjecture,(
% 1.34/0.57    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.34/0.57    inference(negated_conjecture,[],[f13])).
% 1.34/0.57  fof(f13,conjecture,(
% 1.34/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.34/0.57  fof(f68,plain,(
% 1.34/0.57    spl5_2),
% 1.34/0.57    inference(avatar_split_clause,[],[f33,f65])).
% 1.34/0.57  fof(f33,plain,(
% 1.34/0.57    r1_xboole_0(sK0,sK2)),
% 1.34/0.57    inference(cnf_transformation,[],[f22])).
% 1.34/0.57  fof(f63,plain,(
% 1.34/0.57    ~spl5_1),
% 1.34/0.57    inference(avatar_split_clause,[],[f34,f60])).
% 1.34/0.57  fof(f34,plain,(
% 1.34/0.57    ~r1_tarski(sK0,sK1)),
% 1.34/0.57    inference(cnf_transformation,[],[f22])).
% 1.34/0.57  % SZS output end Proof for theBenchmark
% 1.34/0.57  % (30461)------------------------------
% 1.34/0.57  % (30461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.57  % (30461)Termination reason: Refutation
% 1.34/0.57  
% 1.34/0.57  % (30461)Memory used [KB]: 6652
% 1.34/0.57  % (30461)Time elapsed: 0.172 s
% 1.34/0.57  % (30461)------------------------------
% 1.34/0.57  % (30461)------------------------------
% 1.34/0.57  % (30434)Success in time 0.211 s
%------------------------------------------------------------------------------
