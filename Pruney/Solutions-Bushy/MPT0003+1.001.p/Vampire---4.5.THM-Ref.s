%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0003+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 167 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  297 ( 665 expanded)
%              Number of equality atoms :   29 (  57 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2050,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f57,f62,f66,f71,f158,f163,f296,f2033,f2038,f2047,f2048,f2049])).

fof(f2049,plain,
    ( ~ spl5_2
    | spl5_10 ),
    inference(avatar_split_clause,[],[f165,f161,f49])).

fof(f49,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f161,plain,
    ( spl5_10
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f165,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_10 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK0,sK1)
    | spl5_10 ),
    inference(superposition,[],[f162,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f162,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f2048,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | r2_hidden(sK2,k1_xboole_0)
    | ~ r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2047,plain,
    ( spl5_68
    | ~ spl5_69 ),
    inference(avatar_split_clause,[],[f2041,f2031,f2028])).

fof(f2028,plain,
    ( spl5_68
  <=> v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f2031,plain,
    ( spl5_69
  <=> ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f2041,plain,
    ( v1_xboole_0(k3_xboole_0(sK0,sK1))
    | ~ spl5_69 ),
    inference(resolution,[],[f2032,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2032,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f2031])).

fof(f2038,plain,
    ( spl5_10
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f2035,f2028,f161])).

fof(f2035,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_68 ),
    inference(resolution,[],[f2029,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f2029,plain,
    ( v1_xboole_0(k3_xboole_0(sK0,sK1))
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f2028])).

fof(f2033,plain,
    ( spl5_68
    | spl5_69
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f2020,f46,f2031,f2028])).

fof(f46,plain,
    ( spl5_1
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2020,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
        | v1_xboole_0(k3_xboole_0(sK0,sK1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f822,f33])).

fof(f822,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(k3_xboole_0(X0,sK1)),k3_xboole_0(sK0,X1))
        | ~ r2_hidden(X2,k3_xboole_0(X0,sK1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f430,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f430,plain,
    ( ! [X8,X9] :
        ( v1_xboole_0(k3_xboole_0(X8,sK1))
        | ~ r2_hidden(sK3(k3_xboole_0(X8,sK1)),k3_xboole_0(sK0,X9)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f347,f33])).

fof(f347,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k3_xboole_0(X1,sK1))
        | ~ r2_hidden(X0,k3_xboole_0(sK0,X2)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f168,f44])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
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

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f168,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X2,k3_xboole_0(X3,sK1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f296,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(resolution,[],[f205,f80])).

fof(f80,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f78,f70])).

fof(f70,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f78,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl5_5 ),
    inference(resolution,[],[f32,f65])).

fof(f65,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_5
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f205,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl5_16
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f163,plain,
    ( ~ spl5_10
    | spl5_2 ),
    inference(avatar_split_clause,[],[f159,f49,f161])).

fof(f159,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl5_2 ),
    inference(resolution,[],[f56,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f158,plain,
    ( spl5_9
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f148,f59,f53,f156])).

fof(f156,plain,
    ( spl5_9
  <=> r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f53,plain,
    ( spl5_3
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f59,plain,
    ( spl5_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f148,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f142,f60])).

fof(f60,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | r2_hidden(sK2,k3_xboole_0(X0,sK1)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f42,f54])).

fof(f54,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f67,f64,f69])).

fof(f67,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl5_5 ),
    inference(resolution,[],[f31,f65])).

fof(f66,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f62,plain,
    ( ~ spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f24,f59,f49])).

fof(f24,plain,
    ( r2_hidden(sK2,sK0)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( r1_xboole_0(sK0,sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK2,sK0) )
    | ( ! [X3] :
          ( ~ r2_hidden(X3,sK1)
          | ~ r2_hidden(X3,sK0) )
      & ~ r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11])).

fof(f11,plain,
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

fof(f12,plain,
    ( ? [X2] :
        ( r2_hidden(X2,sK1)
        & r2_hidden(X2,sK0) )
   => ( r2_hidden(sK2,sK1)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] :
            ( r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      | ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X3] :
                ~ ( r2_hidden(X3,X1)
                  & r2_hidden(X3,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X2] :
                ~ ( r2_hidden(X2,X1)
                  & r2_hidden(X2,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f57,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f26,f53,f49])).

fof(f26,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f29,f49,f46])).

fof(f29,plain,(
    ! [X3] :
      ( r1_xboole_0(sK0,sK1)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
