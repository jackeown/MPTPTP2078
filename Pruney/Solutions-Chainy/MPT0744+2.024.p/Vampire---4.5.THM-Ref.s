%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:33 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 197 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  432 ( 821 expanded)
%              Number of equality atoms :   78 ( 105 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f96,f97,f146,f154,f161,f166,f172,f177,f185,f190,f222,f256,f263])).

fof(f263,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f74,f255])).

fof(f255,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl4_13
  <=> r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f74,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f256,plain,
    ( ~ spl4_13
    | spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f229,f219,f158,f253])).

fof(f158,plain,
    ( spl4_8
  <=> r2_hidden(sK0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f219,plain,
    ( spl4_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f229,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | spl4_8
    | ~ spl4_10 ),
    inference(superposition,[],[f160,f221])).

fof(f221,plain,
    ( sK0 = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f219])).

fof(f160,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK1,sK1))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f158])).

fof(f222,plain,
    ( ~ spl4_2
    | ~ spl4_1
    | spl4_6
    | spl4_10
    | spl4_7 ),
    inference(avatar_split_clause,[],[f211,f151,f219,f143,f79,f84])).

fof(f84,plain,
    ( spl4_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f79,plain,
    ( spl4_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f143,plain,
    ( spl4_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f151,plain,
    ( spl4_7
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f211,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | spl4_7 ),
    inference(resolution,[],[f50,f153])).

fof(f153,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f151])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f190,plain,
    ( ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f145,f165,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f165,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl4_9
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f145,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f143])).

fof(f185,plain,
    ( ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f145,f159,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f68,f46])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f159,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f158])).

fof(f177,plain,
    ( ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f145,f152,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f152,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f151])).

fof(f172,plain,
    ( ~ spl4_3
    | spl4_7
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl4_3
    | spl4_7
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f153,f160,f90,f72])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f90,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f166,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f147,f93,f163,f84,f79])).

fof(f93,plain,
    ( spl4_4
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f147,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f94,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f94,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f161,plain,
    ( ~ spl4_8
    | spl4_3 ),
    inference(avatar_split_clause,[],[f149,f89,f158])).

fof(f149,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK1,sK1))
    | spl4_3 ),
    inference(resolution,[],[f91,f70])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f154,plain,
    ( ~ spl4_7
    | spl4_3 ),
    inference(avatar_split_clause,[],[f148,f89,f151])).

fof(f148,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_3 ),
    inference(resolution,[],[f91,f71])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f146,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_6
    | spl4_4 ),
    inference(avatar_split_clause,[],[f139,f93,f143,f84,f79])).

fof(f139,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl4_4 ),
    inference(resolution,[],[f45,f95])).

fof(f95,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f97,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f67,f93,f89])).

fof(f67,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f65,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f51,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f41,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK0,X1)
            | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK0,X1)
            | r2_hidden(sK0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK0,X1)
          | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK0,X1)
          | r2_hidden(sK0,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK0,sK1)
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( r1_ordinal1(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f96,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f66,f93,f89])).

fof(f66,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f42,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f40,f84])).

fof(f40,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f39,f79])).

fof(f39,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:52:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.31/0.56  % (6824)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.31/0.56  % (6828)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.56  % (6846)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.57  % (6838)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.57  % (6830)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.31/0.57  % (6827)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.31/0.57  % (6852)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.57  % (6829)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.62/0.58  % (6836)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.62/0.58  % (6852)Refutation not found, incomplete strategy% (6852)------------------------------
% 1.62/0.58  % (6852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (6846)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.58  fof(f264,plain,(
% 1.62/0.58    $false),
% 1.62/0.58    inference(avatar_sat_refutation,[],[f82,f87,f96,f97,f146,f154,f161,f166,f172,f177,f185,f190,f222,f256,f263])).
% 1.62/0.58  fof(f263,plain,(
% 1.62/0.58    spl4_13),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f257])).
% 1.62/0.58  fof(f257,plain,(
% 1.62/0.58    $false | spl4_13),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f74,f255])).
% 1.62/0.58  fof(f255,plain,(
% 1.62/0.58    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | spl4_13),
% 1.62/0.58    inference(avatar_component_clause,[],[f253])).
% 1.62/0.58  fof(f253,plain,(
% 1.62/0.58    spl4_13 <=> r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.62/0.58  fof(f74,plain,(
% 1.62/0.58    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.62/0.58    inference(equality_resolution,[],[f73])).
% 1.62/0.58  fof(f73,plain,(
% 1.62/0.58    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.62/0.58    inference(equality_resolution,[],[f61])).
% 1.62/0.58  fof(f61,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.62/0.58    inference(cnf_transformation,[],[f38])).
% 1.62/0.58  fof(f38,plain,(
% 1.62/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.62/0.58  fof(f37,plain,(
% 1.62/0.58    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f36,plain,(
% 1.62/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.58    inference(rectify,[],[f35])).
% 1.62/0.58  fof(f35,plain,(
% 1.62/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.58    inference(flattening,[],[f34])).
% 1.62/0.58  fof(f34,plain,(
% 1.62/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.58    inference(nnf_transformation,[],[f3])).
% 1.62/0.58  fof(f3,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.62/0.58  fof(f256,plain,(
% 1.62/0.58    ~spl4_13 | spl4_8 | ~spl4_10),
% 1.62/0.58    inference(avatar_split_clause,[],[f229,f219,f158,f253])).
% 1.62/0.58  fof(f158,plain,(
% 1.62/0.58    spl4_8 <=> r2_hidden(sK0,k2_tarski(sK1,sK1))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.62/0.58  fof(f219,plain,(
% 1.62/0.58    spl4_10 <=> sK0 = sK1),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.62/0.58  fof(f229,plain,(
% 1.62/0.58    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | (spl4_8 | ~spl4_10)),
% 1.62/0.58    inference(superposition,[],[f160,f221])).
% 1.62/0.58  fof(f221,plain,(
% 1.62/0.58    sK0 = sK1 | ~spl4_10),
% 1.62/0.58    inference(avatar_component_clause,[],[f219])).
% 1.62/0.58  fof(f160,plain,(
% 1.62/0.58    ~r2_hidden(sK0,k2_tarski(sK1,sK1)) | spl4_8),
% 1.62/0.58    inference(avatar_component_clause,[],[f158])).
% 1.62/0.58  fof(f222,plain,(
% 1.62/0.58    ~spl4_2 | ~spl4_1 | spl4_6 | spl4_10 | spl4_7),
% 1.62/0.58    inference(avatar_split_clause,[],[f211,f151,f219,f143,f79,f84])).
% 1.62/0.58  fof(f84,plain,(
% 1.62/0.58    spl4_2 <=> v3_ordinal1(sK1)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.62/0.58  fof(f79,plain,(
% 1.62/0.58    spl4_1 <=> v3_ordinal1(sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.62/0.58  fof(f143,plain,(
% 1.62/0.58    spl4_6 <=> r2_hidden(sK1,sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.62/0.58  fof(f151,plain,(
% 1.62/0.58    spl4_7 <=> r2_hidden(sK0,sK1)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.62/0.58  fof(f211,plain,(
% 1.62/0.58    sK0 = sK1 | r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | spl4_7),
% 1.62/0.58    inference(resolution,[],[f50,f153])).
% 1.62/0.58  fof(f153,plain,(
% 1.62/0.58    ~r2_hidden(sK0,sK1) | spl4_7),
% 1.62/0.58    inference(avatar_component_clause,[],[f151])).
% 1.62/0.58  fof(f50,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f21])).
% 1.62/0.58  fof(f21,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(flattening,[],[f20])).
% 1.62/0.58  fof(f20,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f8])).
% 1.62/0.58  fof(f8,axiom,(
% 1.62/0.58    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.62/0.58  fof(f190,plain,(
% 1.62/0.58    ~spl4_6 | ~spl4_9),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f187])).
% 1.62/0.58  fof(f187,plain,(
% 1.62/0.58    $false | (~spl4_6 | ~spl4_9)),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f145,f165,f46])).
% 1.62/0.58  fof(f46,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f18])).
% 1.62/0.58  fof(f18,plain,(
% 1.62/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f10])).
% 1.62/0.58  fof(f10,axiom,(
% 1.62/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.62/0.58  fof(f165,plain,(
% 1.62/0.58    r1_tarski(sK0,sK1) | ~spl4_9),
% 1.62/0.58    inference(avatar_component_clause,[],[f163])).
% 1.62/0.58  fof(f163,plain,(
% 1.62/0.58    spl4_9 <=> r1_tarski(sK0,sK1)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.62/0.58  fof(f145,plain,(
% 1.62/0.58    r2_hidden(sK1,sK0) | ~spl4_6),
% 1.62/0.58    inference(avatar_component_clause,[],[f143])).
% 1.62/0.58  fof(f185,plain,(
% 1.62/0.58    ~spl4_6 | ~spl4_8),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f180])).
% 1.62/0.58  fof(f180,plain,(
% 1.62/0.58    $false | (~spl4_6 | ~spl4_8)),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f145,f159,f106])).
% 1.62/0.58  fof(f106,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X0)) | ~r2_hidden(X0,X1)) )),
% 1.62/0.58    inference(resolution,[],[f68,f46])).
% 1.62/0.58  fof(f68,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f48,f52])).
% 1.62/0.58  fof(f52,plain,(
% 1.62/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f4])).
% 1.62/0.58  fof(f4,axiom,(
% 1.62/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.62/0.58  fof(f48,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f28])).
% 1.62/0.58  fof(f28,plain,(
% 1.62/0.58    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.62/0.58    inference(nnf_transformation,[],[f5])).
% 1.62/0.58  fof(f5,axiom,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.62/0.58  fof(f159,plain,(
% 1.62/0.58    r2_hidden(sK0,k2_tarski(sK1,sK1)) | ~spl4_8),
% 1.62/0.58    inference(avatar_component_clause,[],[f158])).
% 1.62/0.58  fof(f177,plain,(
% 1.62/0.58    ~spl4_6 | ~spl4_7),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f174])).
% 1.62/0.58  fof(f174,plain,(
% 1.62/0.58    $false | (~spl4_6 | ~spl4_7)),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f145,f152,f49])).
% 1.62/0.58  fof(f49,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f19])).
% 1.62/0.58  fof(f19,plain,(
% 1.62/0.58    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f1])).
% 1.62/0.58  fof(f1,axiom,(
% 1.62/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.62/0.58  fof(f152,plain,(
% 1.62/0.58    r2_hidden(sK0,sK1) | ~spl4_7),
% 1.62/0.58    inference(avatar_component_clause,[],[f151])).
% 1.62/0.58  fof(f172,plain,(
% 1.62/0.58    ~spl4_3 | spl4_7 | spl4_8),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f169])).
% 1.62/0.58  fof(f169,plain,(
% 1.62/0.58    $false | (~spl4_3 | spl4_7 | spl4_8)),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f153,f160,f90,f72])).
% 1.62/0.58  fof(f72,plain,(
% 1.62/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 1.62/0.58    inference(equality_resolution,[],[f53])).
% 1.62/0.58  fof(f53,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.62/0.58    inference(cnf_transformation,[],[f33])).
% 1.62/0.58  fof(f33,plain,(
% 1.62/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 1.62/0.58  fof(f32,plain,(
% 1.62/0.58    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f31,plain,(
% 1.62/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.62/0.58    inference(rectify,[],[f30])).
% 1.62/0.58  fof(f30,plain,(
% 1.62/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.62/0.58    inference(flattening,[],[f29])).
% 1.62/0.58  fof(f29,plain,(
% 1.62/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.62/0.58    inference(nnf_transformation,[],[f2])).
% 1.62/0.58  fof(f2,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.62/0.58  fof(f90,plain,(
% 1.62/0.58    r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | ~spl4_3),
% 1.62/0.58    inference(avatar_component_clause,[],[f89])).
% 1.62/0.58  fof(f89,plain,(
% 1.62/0.58    spl4_3 <=> r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.62/0.58  fof(f166,plain,(
% 1.62/0.58    ~spl4_1 | ~spl4_2 | spl4_9 | ~spl4_4),
% 1.62/0.58    inference(avatar_split_clause,[],[f147,f93,f163,f84,f79])).
% 1.62/0.58  fof(f93,plain,(
% 1.62/0.58    spl4_4 <=> r1_ordinal1(sK0,sK1)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.62/0.58  fof(f147,plain,(
% 1.62/0.58    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl4_4),
% 1.62/0.58    inference(resolution,[],[f94,f43])).
% 1.62/0.58  fof(f43,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f27])).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(nnf_transformation,[],[f15])).
% 1.62/0.58  fof(f15,plain,(
% 1.62/0.58    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(flattening,[],[f14])).
% 1.62/0.58  fof(f14,plain,(
% 1.62/0.58    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f7])).
% 1.62/0.58  fof(f7,axiom,(
% 1.62/0.58    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.62/0.58  fof(f94,plain,(
% 1.62/0.58    r1_ordinal1(sK0,sK1) | ~spl4_4),
% 1.62/0.58    inference(avatar_component_clause,[],[f93])).
% 1.62/0.58  fof(f161,plain,(
% 1.62/0.58    ~spl4_8 | spl4_3),
% 1.62/0.58    inference(avatar_split_clause,[],[f149,f89,f158])).
% 1.62/0.58  fof(f149,plain,(
% 1.62/0.58    ~r2_hidden(sK0,k2_tarski(sK1,sK1)) | spl4_3),
% 1.62/0.58    inference(resolution,[],[f91,f70])).
% 1.62/0.58  fof(f70,plain,(
% 1.62/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.62/0.58    inference(equality_resolution,[],[f55])).
% 1.62/0.58  fof(f55,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.62/0.58    inference(cnf_transformation,[],[f33])).
% 1.62/0.58  fof(f91,plain,(
% 1.62/0.58    ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | spl4_3),
% 1.62/0.58    inference(avatar_component_clause,[],[f89])).
% 1.62/0.58  fof(f154,plain,(
% 1.62/0.58    ~spl4_7 | spl4_3),
% 1.62/0.58    inference(avatar_split_clause,[],[f148,f89,f151])).
% 1.62/0.58  fof(f148,plain,(
% 1.62/0.58    ~r2_hidden(sK0,sK1) | spl4_3),
% 1.62/0.58    inference(resolution,[],[f91,f71])).
% 1.62/0.58  fof(f71,plain,(
% 1.62/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 1.62/0.58    inference(equality_resolution,[],[f54])).
% 1.62/0.58  fof(f54,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.62/0.58    inference(cnf_transformation,[],[f33])).
% 1.62/0.58  fof(f146,plain,(
% 1.62/0.58    ~spl4_1 | ~spl4_2 | spl4_6 | spl4_4),
% 1.62/0.58    inference(avatar_split_clause,[],[f139,f93,f143,f84,f79])).
% 1.62/0.58  fof(f139,plain,(
% 1.62/0.58    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl4_4),
% 1.62/0.58    inference(resolution,[],[f45,f95])).
% 1.62/0.58  fof(f95,plain,(
% 1.62/0.58    ~r1_ordinal1(sK0,sK1) | spl4_4),
% 1.62/0.58    inference(avatar_component_clause,[],[f93])).
% 1.62/0.58  fof(f45,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f17,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(flattening,[],[f16])).
% 1.62/0.58  fof(f16,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f9])).
% 1.62/0.58  fof(f9,axiom,(
% 1.62/0.58    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.62/0.58  fof(f97,plain,(
% 1.62/0.58    spl4_3 | spl4_4),
% 1.62/0.58    inference(avatar_split_clause,[],[f67,f93,f89])).
% 1.62/0.58  fof(f67,plain,(
% 1.62/0.58    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 1.62/0.58    inference(definition_unfolding,[],[f41,f65])).
% 1.62/0.58  fof(f65,plain,(
% 1.62/0.58    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f51,f52])).
% 1.62/0.58  fof(f51,plain,(
% 1.62/0.58    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f6])).
% 1.62/0.58  fof(f6,axiom,(
% 1.62/0.58    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.62/0.58    inference(cnf_transformation,[],[f26])).
% 1.62/0.58  fof(f26,plain,(
% 1.62/0.58    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).
% 1.62/0.58  fof(f24,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f25,plain,(
% 1.62/0.58    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f23,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.62/0.58    inference(flattening,[],[f22])).
% 1.62/0.58  fof(f22,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.62/0.58    inference(nnf_transformation,[],[f13])).
% 1.62/0.58  fof(f13,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f12])).
% 1.62/0.58  fof(f12,negated_conjecture,(
% 1.62/0.58    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.62/0.58    inference(negated_conjecture,[],[f11])).
% 1.62/0.58  fof(f11,conjecture,(
% 1.62/0.58    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.62/0.58  fof(f96,plain,(
% 1.62/0.58    ~spl4_3 | ~spl4_4),
% 1.62/0.58    inference(avatar_split_clause,[],[f66,f93,f89])).
% 1.62/0.58  fof(f66,plain,(
% 1.62/0.58    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 1.62/0.58    inference(definition_unfolding,[],[f42,f65])).
% 1.62/0.58  fof(f42,plain,(
% 1.62/0.58    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.62/0.58    inference(cnf_transformation,[],[f26])).
% 1.62/0.58  fof(f87,plain,(
% 1.62/0.58    spl4_2),
% 1.62/0.58    inference(avatar_split_clause,[],[f40,f84])).
% 1.62/0.59  fof(f40,plain,(
% 1.62/0.59    v3_ordinal1(sK1)),
% 1.62/0.59    inference(cnf_transformation,[],[f26])).
% 1.62/0.59  fof(f82,plain,(
% 1.62/0.59    spl4_1),
% 1.62/0.59    inference(avatar_split_clause,[],[f39,f79])).
% 1.62/0.59  fof(f39,plain,(
% 1.62/0.59    v3_ordinal1(sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f26])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (6846)------------------------------
% 1.62/0.59  % (6846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (6846)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (6846)Memory used [KB]: 10874
% 1.62/0.59  % (6846)Time elapsed: 0.089 s
% 1.62/0.59  % (6846)------------------------------
% 1.62/0.59  % (6846)------------------------------
% 1.62/0.59  % (6837)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.62/0.59  % (6822)Success in time 0.223 s
%------------------------------------------------------------------------------
