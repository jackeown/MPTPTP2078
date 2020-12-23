%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:42 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 741 expanded)
%              Number of leaves         :   27 ( 205 expanded)
%              Depth                    :   21
%              Number of atoms          :  659 (2839 expanded)
%              Number of equality atoms :   53 ( 437 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f626,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f164,f389,f405,f421,f430,f439,f470,f526,f551,f553,f619])).

fof(f619,plain,
    ( ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f618])).

fof(f618,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f617,f133])).

fof(f133,plain,
    ( v3_ordinal1(sK1(sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_6
  <=> v3_ordinal1(sK1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f617,plain,
    ( ~ v3_ordinal1(sK1(sK2))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f586,f98])).

fof(f98,plain,
    ( v4_ordinal1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f45,f91])).

fof(f91,plain,
    ( sP0(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_2
  <=> sP0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f45,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        & k1_ordinal1(sK1(X0)) = X0
        & v3_ordinal1(sK1(X0)) )
      | ~ sP0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_ordinal1(X1) = X0
          & v3_ordinal1(X1) )
     => ( k1_ordinal1(sK1(X0)) = X0
        & v3_ordinal1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        & ? [X1] :
            ( k1_ordinal1(X1) = X0
            & v3_ordinal1(X1) ) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        & ? [X1] :
            ( k1_ordinal1(X1) = X0
            & v3_ordinal1(X1) ) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f586,plain,
    ( ~ v4_ordinal1(sK2)
    | ~ v3_ordinal1(sK1(sK2))
    | ~ spl4_2 ),
    inference(superposition,[],[f285,f112])).

fof(f112,plain,
    ( sK2 = k2_xboole_0(sK1(sK2),k1_tarski(sK1(sK2)))
    | ~ spl4_2 ),
    inference(resolution,[],[f69,f91])).

fof(f69,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | k2_xboole_0(sK1(X0),k1_tarski(sK1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f50,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f44,plain,(
    ! [X0] :
      ( k1_ordinal1(sK1(X0)) = X0
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f285,plain,(
    ! [X2] :
      ( ~ v4_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))
      | ~ v3_ordinal1(X2) ) ),
    inference(subsumption_resolution,[],[f284,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f51,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f284,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) ) ),
    inference(subsumption_resolution,[],[f281,f84])).

fof(f84,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f68,f50])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f281,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))
      | ~ r2_hidden(X2,k2_xboole_0(X2,k1_tarski(X2)))
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) ) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))
      | ~ r2_hidden(X2,k2_xboole_0(X2,k1_tarski(X2)))
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))
      | ~ v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) ) ),
    inference(resolution,[],[f275,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f52,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK3(X0)),X0)
            & r2_hidden(sK3(X0),X0)
            & v3_ordinal1(sK3(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK3(X0)),X0)
        & r2_hidden(sK3(X0),X0)
        & v3_ordinal1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f275,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f273,f228])).

fof(f228,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f227,f72])).

fof(f227,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ) ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f222,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f222,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f216,f72])).

fof(f216,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) ) ),
    inference(resolution,[],[f210,f84])).

fof(f210,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ v3_ordinal1(X4)
      | ~ v3_ordinal1(X3)
      | r1_ordinal1(X3,X4) ) ),
    inference(resolution,[],[f78,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f50])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f58,f50])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f273,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X1,X1)
      | ~ r1_tarski(X1,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(X1,X1)
      | ~ r1_tarski(X1,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(resolution,[],[f186,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0)
      | ~ r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) ) ),
    inference(extensionality_resolution,[],[f65,f71])).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) != X0 ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f49,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f186,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,X3) ) ),
    inference(subsumption_resolution,[],[f184,f72])).

fof(f184,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3)
      | ~ v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) ) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) ) ),
    inference(resolution,[],[f76,f61])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f56,f50])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f553,plain,
    ( spl4_3
    | spl4_15
    | ~ spl4_16
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f552,f86,f381,f377,f94])).

fof(f94,plain,
    ( spl4_3
  <=> v4_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f377,plain,
    ( spl4_15
  <=> r1_ordinal1(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f381,plain,
    ( spl4_16
  <=> v3_ordinal1(k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f86,plain,
    ( spl4_1
  <=> ! [X1] :
        ( sK2 != k2_xboole_0(X1,k1_tarski(X1))
        | ~ v3_ordinal1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f552,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2))))
    | r1_ordinal1(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2))))
    | v4_ordinal1(sK2)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f368,f46])).

fof(f46,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( sP0(sK2)
      | ( ! [X1] :
            ( k1_ordinal1(X1) != sK2
            | ~ v3_ordinal1(X1) )
        & ~ v4_ordinal1(sK2) ) )
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ( sP0(X0)
          | ( ! [X1] :
                ( k1_ordinal1(X1) != X0
                | ~ v3_ordinal1(X1) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( sP0(sK2)
        | ( ! [X1] :
              ( k1_ordinal1(X1) != sK2
              | ~ v3_ordinal1(X1) )
          & ~ v4_ordinal1(sK2) ) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ( sP0(X0)
        | ( ! [X1] :
              ( k1_ordinal1(X1) != X0
              | ~ v3_ordinal1(X1) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ( sP0(X0)
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(definition_folding,[],[f14,f24])).

fof(f14,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).

fof(f368,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2))))
    | r1_ordinal1(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2))))
    | v4_ordinal1(sK2)
    | ~ v3_ordinal1(sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f364,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_xboole_0(sK3(X0),k1_tarski(sK3(X0))),X0)
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f55,f50])).

fof(f55,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK3(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f364,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ v3_ordinal1(X0)
        | r1_ordinal1(sK2,X0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f363,f46])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(X0,sK2)
        | r1_ordinal1(sK2,X0)
        | ~ v3_ordinal1(sK2) )
    | ~ spl4_1 ),
    inference(duplicate_literal_removal,[],[f360])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(X0,sK2)
        | r1_ordinal1(sK2,X0)
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f357,f78])).

fof(f357,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,k2_xboole_0(X0,k1_tarski(X0)))
        | ~ v3_ordinal1(X0)
        | r2_hidden(X0,sK2) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f355,f46])).

fof(f355,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,k2_xboole_0(X0,k1_tarski(X0)))
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK2)
        | r2_hidden(X0,sK2) )
    | ~ spl4_1 ),
    inference(duplicate_literal_removal,[],[f351])).

fof(f351,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,k2_xboole_0(X0,k1_tarski(X0)))
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK2)
        | ~ v3_ordinal1(X0)
        | r2_hidden(X0,sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f309,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f171,f72])).

fof(f171,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X1,k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X1,k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ) ),
    inference(resolution,[],[f75,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f57,f50])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f309,plain,
    ( ! [X2] :
        ( ~ r1_ordinal1(sK2,k2_xboole_0(X2,k1_tarski(X2)))
        | r2_hidden(sK2,k2_xboole_0(X2,k1_tarski(X2)))
        | ~ v3_ordinal1(X2) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f308,f72])).

fof(f308,plain,
    ( ! [X2] :
        ( ~ r1_ordinal1(sK2,k2_xboole_0(X2,k1_tarski(X2)))
        | ~ v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))
        | r2_hidden(sK2,k2_xboole_0(X2,k1_tarski(X2)))
        | ~ v3_ordinal1(X2) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f288,f46])).

fof(f288,plain,
    ( ! [X2] :
        ( ~ r1_ordinal1(sK2,k2_xboole_0(X2,k1_tarski(X2)))
        | ~ v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))
        | ~ v3_ordinal1(sK2)
        | r2_hidden(sK2,k2_xboole_0(X2,k1_tarski(X2)))
        | ~ v3_ordinal1(X2) )
    | ~ spl4_1 ),
    inference(extensionality_resolution,[],[f203,f87])).

fof(f87,plain,
    ( ! [X1] :
        ( sK2 != k2_xboole_0(X1,k1_tarski(X1))
        | ~ v3_ordinal1(X1) )
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f203,plain,(
    ! [X2,X1] :
      ( ~ r1_ordinal1(X1,X2)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X2)
      | X1 = X2 ) ),
    inference(resolution,[],[f77,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f66,f50])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f59,f50])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f551,plain,
    ( spl4_3
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f550])).

fof(f550,plain,
    ( $false
    | spl4_3
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f548,f46])).

fof(f548,plain,
    ( ~ v3_ordinal1(sK2)
    | spl4_3
    | ~ spl4_22 ),
    inference(resolution,[],[f528,f275])).

fof(f528,plain,
    ( r2_hidden(sK2,sK2)
    | spl4_3
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f527,f46])).

fof(f527,plain,
    ( r2_hidden(sK2,sK2)
    | ~ v3_ordinal1(sK2)
    | spl4_3
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f457,f96])).

fof(f96,plain,
    ( ~ v4_ordinal1(sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f457,plain,
    ( r2_hidden(sK2,sK2)
    | v4_ordinal1(sK2)
    | ~ v3_ordinal1(sK2)
    | ~ spl4_22 ),
    inference(superposition,[],[f54,f434])).

fof(f434,plain,
    ( sK2 = sK3(sK2)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl4_22
  <=> sK2 = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f526,plain,
    ( spl4_3
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | spl4_3
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f523,f46])).

fof(f523,plain,
    ( ~ v3_ordinal1(sK2)
    | spl4_3
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(resolution,[],[f500,f275])).

fof(f500,plain,
    ( r2_hidden(sK2,sK2)
    | spl4_3
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f438,f493])).

fof(f493,plain,
    ( sK2 = sK3(sK2)
    | spl4_3
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f492,f96])).

fof(f492,plain,
    ( sK2 = sK3(sK2)
    | v4_ordinal1(sK2)
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f489,f46])).

fof(f489,plain,
    ( ~ v3_ordinal1(sK2)
    | sK2 = sK3(sK2)
    | v4_ordinal1(sK2)
    | ~ spl4_24 ),
    inference(resolution,[],[f448,f251])).

fof(f251,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK3(X1))
      | ~ v3_ordinal1(X1)
      | sK3(X1) = X1
      | v4_ordinal1(X1) ) ),
    inference(resolution,[],[f232,f65])).

fof(f232,plain,(
    ! [X0] :
      ( r1_tarski(sK3(X0),X0)
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f231,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v3_ordinal1(sK3(X0))
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f231,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v4_ordinal1(X0)
      | r1_tarski(sK3(X0),X0)
      | ~ v3_ordinal1(sK3(X0)) ) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v4_ordinal1(X0)
      | r1_tarski(sK3(X0),X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(sK3(X0)) ) ),
    inference(resolution,[],[f224,f61])).

fof(f224,plain,(
    ! [X5] :
      ( r1_ordinal1(sK3(X5),X5)
      | ~ v3_ordinal1(X5)
      | v4_ordinal1(X5) ) ),
    inference(subsumption_resolution,[],[f220,f53])).

fof(f220,plain,(
    ! [X5] :
      ( ~ v3_ordinal1(X5)
      | ~ v3_ordinal1(sK3(X5))
      | r1_ordinal1(sK3(X5),X5)
      | v4_ordinal1(X5) ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X5] :
      ( ~ v3_ordinal1(X5)
      | ~ v3_ordinal1(sK3(X5))
      | r1_ordinal1(sK3(X5),X5)
      | v4_ordinal1(X5)
      | ~ v3_ordinal1(X5) ) ),
    inference(resolution,[],[f210,f54])).

fof(f448,plain,
    ( r1_tarski(sK2,sK3(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl4_24
  <=> r1_tarski(sK2,sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f438,plain,
    ( r2_hidden(sK2,sK3(sK2))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl4_23
  <=> r2_hidden(sK2,sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f470,plain,
    ( ~ spl4_17
    | spl4_24
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f469,f427,f446,f398])).

fof(f398,plain,
    ( spl4_17
  <=> v3_ordinal1(sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f427,plain,
    ( spl4_21
  <=> r1_ordinal1(sK2,sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f469,plain,
    ( r1_tarski(sK2,sK3(sK2))
    | ~ v3_ordinal1(sK3(sK2))
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f466,f46])).

fof(f466,plain,
    ( r1_tarski(sK2,sK3(sK2))
    | ~ v3_ordinal1(sK3(sK2))
    | ~ v3_ordinal1(sK2)
    | ~ spl4_21 ),
    inference(resolution,[],[f429,f61])).

fof(f429,plain,
    ( r1_ordinal1(sK2,sK3(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f427])).

fof(f439,plain,
    ( spl4_22
    | spl4_23
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f423,f402,f436,f432])).

fof(f402,plain,
    ( spl4_18
  <=> r2_hidden(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f423,plain,
    ( r2_hidden(sK2,sK3(sK2))
    | sK2 = sK3(sK2)
    | ~ spl4_18 ),
    inference(resolution,[],[f404,f81])).

fof(f404,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2))))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f402])).

fof(f430,plain,
    ( ~ spl4_17
    | spl4_21
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f425,f402,f427,f398])).

fof(f425,plain,
    ( r1_ordinal1(sK2,sK3(sK2))
    | ~ v3_ordinal1(sK3(sK2))
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f422,f46])).

fof(f422,plain,
    ( r1_ordinal1(sK2,sK3(sK2))
    | ~ v3_ordinal1(sK3(sK2))
    | ~ v3_ordinal1(sK2)
    | ~ spl4_18 ),
    inference(resolution,[],[f404,f78])).

fof(f421,plain,
    ( spl4_3
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | spl4_3
    | spl4_17 ),
    inference(subsumption_resolution,[],[f419,f46])).

fof(f419,plain,
    ( ~ v3_ordinal1(sK2)
    | spl4_3
    | spl4_17 ),
    inference(subsumption_resolution,[],[f418,f96])).

fof(f418,plain,
    ( v4_ordinal1(sK2)
    | ~ v3_ordinal1(sK2)
    | spl4_17 ),
    inference(resolution,[],[f400,f53])).

fof(f400,plain,
    ( ~ v3_ordinal1(sK3(sK2))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f398])).

fof(f405,plain,
    ( ~ spl4_17
    | spl4_18
    | ~ spl4_1
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f394,f377,f86,f402,f398])).

fof(f394,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2))))
    | ~ v3_ordinal1(sK3(sK2))
    | ~ spl4_1
    | ~ spl4_15 ),
    inference(resolution,[],[f379,f309])).

fof(f379,plain,
    ( r1_ordinal1(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2))))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f377])).

fof(f389,plain,
    ( spl4_3
    | spl4_16 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | spl4_3
    | spl4_16 ),
    inference(subsumption_resolution,[],[f387,f46])).

fof(f387,plain,
    ( ~ v3_ordinal1(sK2)
    | spl4_3
    | spl4_16 ),
    inference(subsumption_resolution,[],[f386,f96])).

fof(f386,plain,
    ( v4_ordinal1(sK2)
    | ~ v3_ordinal1(sK2)
    | spl4_16 ),
    inference(resolution,[],[f385,f53])).

fof(f385,plain,
    ( ~ v3_ordinal1(sK3(sK2))
    | spl4_16 ),
    inference(resolution,[],[f383,f72])).

fof(f383,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2))))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f381])).

fof(f164,plain,
    ( ~ spl4_2
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl4_2
    | spl4_6 ),
    inference(subsumption_resolution,[],[f162,f91])).

fof(f162,plain,
    ( ~ sP0(sK2)
    | spl4_6 ),
    inference(resolution,[],[f134,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v3_ordinal1(sK1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f134,plain,
    ( ~ v3_ordinal1(sK1(sK2))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f97,plain,
    ( ~ spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f47,f89,f94])).

fof(f47,plain,
    ( sP0(sK2)
    | ~ v4_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f70,f89,f86])).

fof(f70,plain,(
    ! [X1] :
      ( sP0(sK2)
      | sK2 != k2_xboole_0(X1,k1_tarski(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f48,plain,(
    ! [X1] :
      ( sP0(sK2)
      | k1_ordinal1(X1) != sK2
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:09:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.47  % (21914)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (21913)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.50  % (21922)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.51  % (21918)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.51  % (21924)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.21/0.51  % (21912)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.21/0.51  % (21909)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.21/0.51  % (21919)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.21/0.51  % (21930)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.21/0.51  % (21915)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.51  % (21911)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.21/0.51  % (21920)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.21/0.51  % (21929)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.21/0.51  % (21919)Refutation not found, incomplete strategy% (21919)------------------------------
% 1.21/0.51  % (21919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.51  % (21919)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.51  
% 1.21/0.51  % (21919)Memory used [KB]: 10746
% 1.21/0.51  % (21919)Time elapsed: 0.108 s
% 1.21/0.51  % (21919)------------------------------
% 1.21/0.51  % (21919)------------------------------
% 1.21/0.52  % (21934)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.21/0.52  % (21938)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.21/0.52  % (21928)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.21/0.52  % (21921)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.21/0.52  % (21910)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.21/0.52  % (21925)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.21/0.52  % (21933)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.21/0.52  % (21925)Refutation not found, incomplete strategy% (21925)------------------------------
% 1.21/0.52  % (21925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (21925)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (21925)Memory used [KB]: 10618
% 1.21/0.52  % (21925)Time elapsed: 0.125 s
% 1.21/0.52  % (21925)------------------------------
% 1.21/0.52  % (21925)------------------------------
% 1.36/0.53  % (21915)Refutation found. Thanks to Tanya!
% 1.36/0.53  % SZS status Theorem for theBenchmark
% 1.36/0.53  % SZS output start Proof for theBenchmark
% 1.36/0.53  fof(f626,plain,(
% 1.36/0.53    $false),
% 1.36/0.53    inference(avatar_sat_refutation,[],[f92,f97,f164,f389,f405,f421,f430,f439,f470,f526,f551,f553,f619])).
% 1.36/0.53  fof(f619,plain,(
% 1.36/0.53    ~spl4_2 | ~spl4_6),
% 1.36/0.53    inference(avatar_contradiction_clause,[],[f618])).
% 1.36/0.53  fof(f618,plain,(
% 1.36/0.53    $false | (~spl4_2 | ~spl4_6)),
% 1.36/0.53    inference(subsumption_resolution,[],[f617,f133])).
% 1.36/0.53  fof(f133,plain,(
% 1.36/0.53    v3_ordinal1(sK1(sK2)) | ~spl4_6),
% 1.36/0.53    inference(avatar_component_clause,[],[f132])).
% 1.36/0.53  fof(f132,plain,(
% 1.36/0.53    spl4_6 <=> v3_ordinal1(sK1(sK2))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.36/0.53  fof(f617,plain,(
% 1.36/0.53    ~v3_ordinal1(sK1(sK2)) | ~spl4_2),
% 1.36/0.53    inference(subsumption_resolution,[],[f586,f98])).
% 1.36/0.53  fof(f98,plain,(
% 1.36/0.53    v4_ordinal1(sK2) | ~spl4_2),
% 1.36/0.53    inference(resolution,[],[f45,f91])).
% 1.36/0.53  fof(f91,plain,(
% 1.36/0.53    sP0(sK2) | ~spl4_2),
% 1.36/0.53    inference(avatar_component_clause,[],[f89])).
% 1.36/0.53  fof(f89,plain,(
% 1.36/0.53    spl4_2 <=> sP0(sK2)),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.36/0.53  fof(f45,plain,(
% 1.36/0.53    ( ! [X0] : (~sP0(X0) | v4_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f28])).
% 1.36/0.53  fof(f28,plain,(
% 1.36/0.53    ! [X0] : ((v4_ordinal1(X0) & (k1_ordinal1(sK1(X0)) = X0 & v3_ordinal1(sK1(X0)))) | ~sP0(X0))),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 1.36/0.53  fof(f27,plain,(
% 1.36/0.53    ! [X0] : (? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1)) => (k1_ordinal1(sK1(X0)) = X0 & v3_ordinal1(sK1(X0))))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f26,plain,(
% 1.36/0.53    ! [X0] : ((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | ~sP0(X0))),
% 1.36/0.53    inference(nnf_transformation,[],[f24])).
% 1.36/0.53  fof(f24,plain,(
% 1.36/0.53    ! [X0] : ((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | ~sP0(X0))),
% 1.36/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.36/0.53  fof(f586,plain,(
% 1.36/0.53    ~v4_ordinal1(sK2) | ~v3_ordinal1(sK1(sK2)) | ~spl4_2),
% 1.36/0.53    inference(superposition,[],[f285,f112])).
% 1.36/0.53  fof(f112,plain,(
% 1.36/0.53    sK2 = k2_xboole_0(sK1(sK2),k1_tarski(sK1(sK2))) | ~spl4_2),
% 1.36/0.53    inference(resolution,[],[f69,f91])).
% 1.36/0.53  fof(f69,plain,(
% 1.36/0.53    ( ! [X0] : (~sP0(X0) | k2_xboole_0(sK1(X0),k1_tarski(sK1(X0))) = X0) )),
% 1.36/0.53    inference(definition_unfolding,[],[f44,f50])).
% 1.36/0.53  fof(f50,plain,(
% 1.36/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f3])).
% 1.36/0.53  fof(f3,axiom,(
% 1.36/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.36/0.53  fof(f44,plain,(
% 1.36/0.53    ( ! [X0] : (k1_ordinal1(sK1(X0)) = X0 | ~sP0(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f28])).
% 1.36/0.53  fof(f285,plain,(
% 1.36/0.53    ( ! [X2] : (~v4_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) | ~v3_ordinal1(X2)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f284,f72])).
% 1.36/0.53  fof(f72,plain,(
% 1.36/0.53    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f51,f50])).
% 1.36/0.53  fof(f51,plain,(
% 1.36/0.53    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f15])).
% 1.36/0.53  fof(f15,plain,(
% 1.36/0.53    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f7])).
% 1.36/0.53  fof(f7,axiom,(
% 1.36/0.53    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 1.36/0.53  fof(f284,plain,(
% 1.36/0.53    ( ! [X2] : (~v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) | ~v3_ordinal1(X2) | ~v4_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f281,f84])).
% 1.36/0.53  fof(f84,plain,(
% 1.36/0.53    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 1.36/0.53    inference(equality_resolution,[],[f79])).
% 1.36/0.53  fof(f79,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 1.36/0.53    inference(definition_unfolding,[],[f68,f50])).
% 1.36/0.53  fof(f68,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 1.36/0.53    inference(cnf_transformation,[],[f42])).
% 1.36/0.53  fof(f42,plain,(
% 1.36/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.36/0.53    inference(flattening,[],[f41])).
% 1.36/0.53  fof(f41,plain,(
% 1.36/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.36/0.53    inference(nnf_transformation,[],[f5])).
% 1.36/0.53  fof(f5,axiom,(
% 1.36/0.53    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.36/0.53  fof(f281,plain,(
% 1.36/0.53    ( ! [X2] : (~v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) | ~r2_hidden(X2,k2_xboole_0(X2,k1_tarski(X2))) | ~v3_ordinal1(X2) | ~v4_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f280])).
% 1.36/0.53  fof(f280,plain,(
% 1.36/0.53    ( ! [X2] : (~v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) | ~r2_hidden(X2,k2_xboole_0(X2,k1_tarski(X2))) | ~v3_ordinal1(X2) | ~v4_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) | ~v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))) )),
% 1.36/0.53    inference(resolution,[],[f275,f74])).
% 1.36/0.53  fof(f74,plain,(
% 1.36/0.53    ( ! [X2,X0] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f52,f50])).
% 1.36/0.53  fof(f52,plain,(
% 1.36/0.53    ( ! [X2,X0] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f35])).
% 1.36/0.53  fof(f35,plain,(
% 1.36/0.53    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK3(X0)),X0) & r2_hidden(sK3(X0),X0) & v3_ordinal1(sK3(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 1.36/0.53  fof(f34,plain,(
% 1.36/0.53    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK3(X0)),X0) & r2_hidden(sK3(X0),X0) & v3_ordinal1(sK3(X0))))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f33,plain,(
% 1.36/0.53    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(rectify,[],[f32])).
% 1.36/0.53  fof(f32,plain,(
% 1.36/0.53    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(nnf_transformation,[],[f17])).
% 1.36/0.53  fof(f17,plain,(
% 1.36/0.53    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(flattening,[],[f16])).
% 1.36/0.53  fof(f16,plain,(
% 1.36/0.53    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f10])).
% 1.36/0.53  fof(f10,axiom,(
% 1.36/0.53    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).
% 1.36/0.53  fof(f275,plain,(
% 1.36/0.53    ( ! [X1] : (~r2_hidden(X1,X1) | ~v3_ordinal1(X1)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f273,f228])).
% 1.36/0.53  fof(f228,plain,(
% 1.36/0.53    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f227,f72])).
% 1.36/0.53  fof(f227,plain,(
% 1.36/0.53    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f225])).
% 1.36/0.53  fof(f225,plain,(
% 1.36/0.53    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(resolution,[],[f222,f61])).
% 1.36/0.53  fof(f61,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f38])).
% 1.36/0.53  fof(f38,plain,(
% 1.36/0.53    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(nnf_transformation,[],[f23])).
% 1.36/0.53  fof(f23,plain,(
% 1.36/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(flattening,[],[f22])).
% 1.36/0.53  fof(f22,plain,(
% 1.36/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f4])).
% 1.36/0.53  fof(f4,axiom,(
% 1.36/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.36/0.53  fof(f222,plain,(
% 1.36/0.53    ( ! [X0] : (r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f216,f72])).
% 1.36/0.53  fof(f216,plain,(
% 1.36/0.53    ( ! [X0] : (~v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0) | r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 1.36/0.53    inference(resolution,[],[f210,f84])).
% 1.36/0.53  fof(f210,plain,(
% 1.36/0.53    ( ! [X4,X3] : (~r2_hidden(X3,X4) | ~v3_ordinal1(X4) | ~v3_ordinal1(X3) | r1_ordinal1(X3,X4)) )),
% 1.36/0.53    inference(resolution,[],[f78,f80])).
% 1.36/0.53  fof(f80,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f67,f50])).
% 1.36/0.53  fof(f67,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f42])).
% 1.36/0.53  fof(f78,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f58,f50])).
% 1.36/0.53  fof(f58,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f37])).
% 1.36/0.53  fof(f37,plain,(
% 1.36/0.53    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(nnf_transformation,[],[f19])).
% 1.36/0.53  fof(f19,plain,(
% 1.36/0.53    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f9])).
% 1.36/0.53  fof(f9,axiom,(
% 1.36/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.36/0.53  fof(f273,plain,(
% 1.36/0.53    ( ! [X1] : (~v3_ordinal1(X1) | ~r2_hidden(X1,X1) | ~r1_tarski(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f266])).
% 1.36/0.53  fof(f266,plain,(
% 1.36/0.53    ( ! [X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X1) | ~r2_hidden(X1,X1) | ~r1_tarski(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 1.36/0.53    inference(resolution,[],[f186,f99])).
% 1.36/0.53  fof(f99,plain,(
% 1.36/0.53    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) | ~r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 1.36/0.53    inference(extensionality_resolution,[],[f65,f71])).
% 1.36/0.53  fof(f71,plain,(
% 1.36/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) != X0) )),
% 1.36/0.53    inference(definition_unfolding,[],[f49,f50])).
% 1.36/0.53  fof(f49,plain,(
% 1.36/0.53    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 1.36/0.53    inference(cnf_transformation,[],[f6])).
% 1.36/0.53  fof(f6,axiom,(
% 1.36/0.53    ! [X0] : k1_ordinal1(X0) != X0),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).
% 1.36/0.53  fof(f65,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f40])).
% 1.36/0.53  fof(f40,plain,(
% 1.36/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.53    inference(flattening,[],[f39])).
% 1.36/0.53  fof(f39,plain,(
% 1.36/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.53    inference(nnf_transformation,[],[f1])).
% 1.36/0.53  fof(f1,axiom,(
% 1.36/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.53  fof(f186,plain,(
% 1.36/0.53    ( ! [X2,X3] : (r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X3)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f184,f72])).
% 1.36/0.53  fof(f184,plain,(
% 1.36/0.53    ( ! [X2,X3] : (~r2_hidden(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3) | ~v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f183])).
% 1.36/0.53  fof(f183,plain,(
% 1.36/0.53    ( ! [X2,X3] : (~r2_hidden(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))) )),
% 1.36/0.53    inference(resolution,[],[f76,f61])).
% 1.36/0.53  fof(f76,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f56,f50])).
% 1.36/0.53  fof(f56,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f36])).
% 1.36/0.53  fof(f36,plain,(
% 1.36/0.53    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(nnf_transformation,[],[f18])).
% 1.36/0.53  fof(f18,plain,(
% 1.36/0.53    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f8])).
% 1.36/0.53  fof(f8,axiom,(
% 1.36/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 1.36/0.53  fof(f553,plain,(
% 1.36/0.53    spl4_3 | spl4_15 | ~spl4_16 | ~spl4_1),
% 1.36/0.53    inference(avatar_split_clause,[],[f552,f86,f381,f377,f94])).
% 1.36/0.53  fof(f94,plain,(
% 1.36/0.53    spl4_3 <=> v4_ordinal1(sK2)),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.36/0.53  fof(f377,plain,(
% 1.36/0.53    spl4_15 <=> r1_ordinal1(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2))))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.36/0.53  fof(f381,plain,(
% 1.36/0.53    spl4_16 <=> v3_ordinal1(k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2))))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.36/0.53  fof(f86,plain,(
% 1.36/0.53    spl4_1 <=> ! [X1] : (sK2 != k2_xboole_0(X1,k1_tarski(X1)) | ~v3_ordinal1(X1))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.36/0.53  fof(f552,plain,(
% 1.36/0.53    ~v3_ordinal1(k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2)))) | r1_ordinal1(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2)))) | v4_ordinal1(sK2) | ~spl4_1),
% 1.36/0.53    inference(subsumption_resolution,[],[f368,f46])).
% 1.36/0.53  fof(f46,plain,(
% 1.36/0.53    v3_ordinal1(sK2)),
% 1.36/0.53    inference(cnf_transformation,[],[f31])).
% 1.36/0.53  fof(f31,plain,(
% 1.36/0.53    (sP0(sK2) | (! [X1] : (k1_ordinal1(X1) != sK2 | ~v3_ordinal1(X1)) & ~v4_ordinal1(sK2))) & v3_ordinal1(sK2)),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 1.36/0.53  fof(f30,plain,(
% 1.36/0.53    ? [X0] : ((sP0(X0) | (! [X1] : (k1_ordinal1(X1) != X0 | ~v3_ordinal1(X1)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => ((sP0(sK2) | (! [X1] : (k1_ordinal1(X1) != sK2 | ~v3_ordinal1(X1)) & ~v4_ordinal1(sK2))) & v3_ordinal1(sK2))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f29,plain,(
% 1.36/0.53    ? [X0] : ((sP0(X0) | (! [X1] : (k1_ordinal1(X1) != X0 | ~v3_ordinal1(X1)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 1.36/0.53    inference(rectify,[],[f25])).
% 1.36/0.53  fof(f25,plain,(
% 1.36/0.53    ? [X0] : ((sP0(X0) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 1.36/0.53    inference(definition_folding,[],[f14,f24])).
% 1.36/0.53  fof(f14,plain,(
% 1.36/0.53    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f13])).
% 1.36/0.53  fof(f13,plain,(
% 1.36/0.53    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 1.36/0.53    inference(rectify,[],[f12])).
% 1.36/0.53  fof(f12,negated_conjecture,(
% 1.36/0.53    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 1.36/0.53    inference(negated_conjecture,[],[f11])).
% 1.36/0.53  fof(f11,conjecture,(
% 1.36/0.53    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).
% 1.36/0.53  fof(f368,plain,(
% 1.36/0.53    ~v3_ordinal1(k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2)))) | r1_ordinal1(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2)))) | v4_ordinal1(sK2) | ~v3_ordinal1(sK2) | ~spl4_1),
% 1.36/0.53    inference(resolution,[],[f364,f73])).
% 1.36/0.53  fof(f73,plain,(
% 1.36/0.53    ( ! [X0] : (~r2_hidden(k2_xboole_0(sK3(X0),k1_tarski(sK3(X0))),X0) | v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f55,f50])).
% 1.36/0.53  fof(f55,plain,(
% 1.36/0.53    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k1_ordinal1(sK3(X0)),X0) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f35])).
% 1.36/0.53  fof(f364,plain,(
% 1.36/0.53    ( ! [X0] : (r2_hidden(X0,sK2) | ~v3_ordinal1(X0) | r1_ordinal1(sK2,X0)) ) | ~spl4_1),
% 1.36/0.53    inference(subsumption_resolution,[],[f363,f46])).
% 1.36/0.53  fof(f363,plain,(
% 1.36/0.53    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK2) | r1_ordinal1(sK2,X0) | ~v3_ordinal1(sK2)) ) | ~spl4_1),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f360])).
% 1.36/0.53  fof(f360,plain,(
% 1.36/0.53    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK2) | r1_ordinal1(sK2,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(sK2)) ) | ~spl4_1),
% 1.36/0.53    inference(resolution,[],[f357,f78])).
% 1.36/0.53  fof(f357,plain,(
% 1.36/0.53    ( ! [X0] : (r2_hidden(sK2,k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0) | r2_hidden(X0,sK2)) ) | ~spl4_1),
% 1.36/0.53    inference(subsumption_resolution,[],[f355,f46])).
% 1.36/0.53  fof(f355,plain,(
% 1.36/0.53    ( ! [X0] : (r2_hidden(sK2,k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0) | ~v3_ordinal1(sK2) | r2_hidden(X0,sK2)) ) | ~spl4_1),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f351])).
% 1.36/0.53  fof(f351,plain,(
% 1.36/0.53    ( ! [X0] : (r2_hidden(sK2,k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0) | ~v3_ordinal1(sK2) | ~v3_ordinal1(X0) | r2_hidden(X0,sK2)) ) | ~spl4_1),
% 1.36/0.53    inference(resolution,[],[f309,f172])).
% 1.36/0.53  fof(f172,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r1_ordinal1(X1,k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X0,X1)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f171,f72])).
% 1.36/0.53  fof(f171,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X1,k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f165])).
% 1.36/0.53  fof(f165,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X1,k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X1) | ~v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))) )),
% 1.36/0.53    inference(resolution,[],[f75,f60])).
% 1.36/0.53  fof(f60,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f21])).
% 1.36/0.53  fof(f21,plain,(
% 1.36/0.53    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.36/0.53    inference(flattening,[],[f20])).
% 1.36/0.53  fof(f20,plain,(
% 1.36/0.53    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f2])).
% 1.36/0.53  fof(f2,axiom,(
% 1.36/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 1.36/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 1.36/0.53  fof(f75,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f57,f50])).
% 1.36/0.53  fof(f57,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f36])).
% 1.36/0.53  fof(f309,plain,(
% 1.36/0.53    ( ! [X2] : (~r1_ordinal1(sK2,k2_xboole_0(X2,k1_tarski(X2))) | r2_hidden(sK2,k2_xboole_0(X2,k1_tarski(X2))) | ~v3_ordinal1(X2)) ) | ~spl4_1),
% 1.36/0.53    inference(subsumption_resolution,[],[f308,f72])).
% 1.36/0.53  fof(f308,plain,(
% 1.36/0.53    ( ! [X2] : (~r1_ordinal1(sK2,k2_xboole_0(X2,k1_tarski(X2))) | ~v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) | r2_hidden(sK2,k2_xboole_0(X2,k1_tarski(X2))) | ~v3_ordinal1(X2)) ) | ~spl4_1),
% 1.36/0.53    inference(subsumption_resolution,[],[f288,f46])).
% 1.36/0.53  fof(f288,plain,(
% 1.36/0.53    ( ! [X2] : (~r1_ordinal1(sK2,k2_xboole_0(X2,k1_tarski(X2))) | ~v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2))) | ~v3_ordinal1(sK2) | r2_hidden(sK2,k2_xboole_0(X2,k1_tarski(X2))) | ~v3_ordinal1(X2)) ) | ~spl4_1),
% 1.36/0.53    inference(extensionality_resolution,[],[f203,f87])).
% 1.36/0.53  fof(f87,plain,(
% 1.36/0.53    ( ! [X1] : (sK2 != k2_xboole_0(X1,k1_tarski(X1)) | ~v3_ordinal1(X1)) ) | ~spl4_1),
% 1.36/0.53    inference(avatar_component_clause,[],[f86])).
% 1.36/0.53  fof(f203,plain,(
% 1.36/0.53    ( ! [X2,X1] : (~r1_ordinal1(X1,X2) | ~v3_ordinal1(X2) | ~v3_ordinal1(X1) | r2_hidden(X1,X2) | X1 = X2) )),
% 1.36/0.53    inference(resolution,[],[f77,f81])).
% 1.36/0.53  fof(f81,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 1.36/0.53    inference(definition_unfolding,[],[f66,f50])).
% 1.36/0.53  fof(f66,plain,(
% 1.36/0.53    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f42])).
% 1.36/0.53  fof(f77,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f59,f50])).
% 1.36/0.53  fof(f59,plain,(
% 1.36/0.53    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f37])).
% 1.36/0.53  fof(f551,plain,(
% 1.36/0.53    spl4_3 | ~spl4_22),
% 1.36/0.53    inference(avatar_contradiction_clause,[],[f550])).
% 1.36/0.53  fof(f550,plain,(
% 1.36/0.53    $false | (spl4_3 | ~spl4_22)),
% 1.36/0.53    inference(subsumption_resolution,[],[f548,f46])).
% 1.36/0.53  fof(f548,plain,(
% 1.36/0.53    ~v3_ordinal1(sK2) | (spl4_3 | ~spl4_22)),
% 1.36/0.53    inference(resolution,[],[f528,f275])).
% 1.36/0.53  fof(f528,plain,(
% 1.36/0.53    r2_hidden(sK2,sK2) | (spl4_3 | ~spl4_22)),
% 1.36/0.53    inference(subsumption_resolution,[],[f527,f46])).
% 1.36/0.53  fof(f527,plain,(
% 1.36/0.53    r2_hidden(sK2,sK2) | ~v3_ordinal1(sK2) | (spl4_3 | ~spl4_22)),
% 1.36/0.53    inference(subsumption_resolution,[],[f457,f96])).
% 1.36/0.53  fof(f96,plain,(
% 1.36/0.53    ~v4_ordinal1(sK2) | spl4_3),
% 1.36/0.53    inference(avatar_component_clause,[],[f94])).
% 1.36/0.53  fof(f457,plain,(
% 1.36/0.53    r2_hidden(sK2,sK2) | v4_ordinal1(sK2) | ~v3_ordinal1(sK2) | ~spl4_22),
% 1.36/0.53    inference(superposition,[],[f54,f434])).
% 1.36/0.53  fof(f434,plain,(
% 1.36/0.53    sK2 = sK3(sK2) | ~spl4_22),
% 1.36/0.53    inference(avatar_component_clause,[],[f432])).
% 1.36/0.53  fof(f432,plain,(
% 1.36/0.53    spl4_22 <=> sK2 = sK3(sK2)),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.36/0.53  fof(f54,plain,(
% 1.36/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f35])).
% 1.36/0.53  fof(f526,plain,(
% 1.36/0.53    spl4_3 | ~spl4_23 | ~spl4_24),
% 1.36/0.53    inference(avatar_contradiction_clause,[],[f525])).
% 1.36/0.53  fof(f525,plain,(
% 1.36/0.53    $false | (spl4_3 | ~spl4_23 | ~spl4_24)),
% 1.36/0.53    inference(subsumption_resolution,[],[f523,f46])).
% 1.36/0.53  fof(f523,plain,(
% 1.36/0.53    ~v3_ordinal1(sK2) | (spl4_3 | ~spl4_23 | ~spl4_24)),
% 1.36/0.53    inference(resolution,[],[f500,f275])).
% 1.36/0.53  fof(f500,plain,(
% 1.36/0.53    r2_hidden(sK2,sK2) | (spl4_3 | ~spl4_23 | ~spl4_24)),
% 1.36/0.53    inference(backward_demodulation,[],[f438,f493])).
% 1.36/0.53  fof(f493,plain,(
% 1.36/0.53    sK2 = sK3(sK2) | (spl4_3 | ~spl4_24)),
% 1.36/0.53    inference(subsumption_resolution,[],[f492,f96])).
% 1.36/0.53  fof(f492,plain,(
% 1.36/0.53    sK2 = sK3(sK2) | v4_ordinal1(sK2) | ~spl4_24),
% 1.36/0.53    inference(subsumption_resolution,[],[f489,f46])).
% 1.36/0.53  fof(f489,plain,(
% 1.36/0.53    ~v3_ordinal1(sK2) | sK2 = sK3(sK2) | v4_ordinal1(sK2) | ~spl4_24),
% 1.36/0.53    inference(resolution,[],[f448,f251])).
% 1.36/0.53  fof(f251,plain,(
% 1.36/0.53    ( ! [X1] : (~r1_tarski(X1,sK3(X1)) | ~v3_ordinal1(X1) | sK3(X1) = X1 | v4_ordinal1(X1)) )),
% 1.36/0.53    inference(resolution,[],[f232,f65])).
% 1.36/0.53  fof(f232,plain,(
% 1.36/0.53    ( ! [X0] : (r1_tarski(sK3(X0),X0) | v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f231,f53])).
% 1.36/0.53  fof(f53,plain,(
% 1.36/0.53    ( ! [X0] : (v3_ordinal1(sK3(X0)) | v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f35])).
% 1.36/0.53  fof(f231,plain,(
% 1.36/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v4_ordinal1(X0) | r1_tarski(sK3(X0),X0) | ~v3_ordinal1(sK3(X0))) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f230])).
% 1.36/0.53  fof(f230,plain,(
% 1.36/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v4_ordinal1(X0) | r1_tarski(sK3(X0),X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(sK3(X0))) )),
% 1.36/0.53    inference(resolution,[],[f224,f61])).
% 1.36/0.53  fof(f224,plain,(
% 1.36/0.53    ( ! [X5] : (r1_ordinal1(sK3(X5),X5) | ~v3_ordinal1(X5) | v4_ordinal1(X5)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f220,f53])).
% 1.36/0.53  fof(f220,plain,(
% 1.36/0.53    ( ! [X5] : (~v3_ordinal1(X5) | ~v3_ordinal1(sK3(X5)) | r1_ordinal1(sK3(X5),X5) | v4_ordinal1(X5)) )),
% 1.36/0.53    inference(duplicate_literal_removal,[],[f219])).
% 1.36/0.53  fof(f219,plain,(
% 1.36/0.53    ( ! [X5] : (~v3_ordinal1(X5) | ~v3_ordinal1(sK3(X5)) | r1_ordinal1(sK3(X5),X5) | v4_ordinal1(X5) | ~v3_ordinal1(X5)) )),
% 1.36/0.53    inference(resolution,[],[f210,f54])).
% 1.36/0.53  fof(f448,plain,(
% 1.36/0.53    r1_tarski(sK2,sK3(sK2)) | ~spl4_24),
% 1.36/0.53    inference(avatar_component_clause,[],[f446])).
% 1.36/0.53  fof(f446,plain,(
% 1.36/0.53    spl4_24 <=> r1_tarski(sK2,sK3(sK2))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.36/0.53  fof(f438,plain,(
% 1.36/0.53    r2_hidden(sK2,sK3(sK2)) | ~spl4_23),
% 1.36/0.53    inference(avatar_component_clause,[],[f436])).
% 1.36/0.53  fof(f436,plain,(
% 1.36/0.53    spl4_23 <=> r2_hidden(sK2,sK3(sK2))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.36/0.53  fof(f470,plain,(
% 1.36/0.53    ~spl4_17 | spl4_24 | ~spl4_21),
% 1.36/0.53    inference(avatar_split_clause,[],[f469,f427,f446,f398])).
% 1.36/0.53  fof(f398,plain,(
% 1.36/0.53    spl4_17 <=> v3_ordinal1(sK3(sK2))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.36/0.53  fof(f427,plain,(
% 1.36/0.53    spl4_21 <=> r1_ordinal1(sK2,sK3(sK2))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.36/0.53  fof(f469,plain,(
% 1.36/0.53    r1_tarski(sK2,sK3(sK2)) | ~v3_ordinal1(sK3(sK2)) | ~spl4_21),
% 1.36/0.53    inference(subsumption_resolution,[],[f466,f46])).
% 1.36/0.53  fof(f466,plain,(
% 1.36/0.53    r1_tarski(sK2,sK3(sK2)) | ~v3_ordinal1(sK3(sK2)) | ~v3_ordinal1(sK2) | ~spl4_21),
% 1.36/0.53    inference(resolution,[],[f429,f61])).
% 1.36/0.53  fof(f429,plain,(
% 1.36/0.53    r1_ordinal1(sK2,sK3(sK2)) | ~spl4_21),
% 1.36/0.53    inference(avatar_component_clause,[],[f427])).
% 1.36/0.53  fof(f439,plain,(
% 1.36/0.53    spl4_22 | spl4_23 | ~spl4_18),
% 1.36/0.53    inference(avatar_split_clause,[],[f423,f402,f436,f432])).
% 1.36/0.53  fof(f402,plain,(
% 1.36/0.53    spl4_18 <=> r2_hidden(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2))))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.36/0.53  fof(f423,plain,(
% 1.36/0.53    r2_hidden(sK2,sK3(sK2)) | sK2 = sK3(sK2) | ~spl4_18),
% 1.36/0.53    inference(resolution,[],[f404,f81])).
% 1.36/0.53  fof(f404,plain,(
% 1.36/0.53    r2_hidden(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2)))) | ~spl4_18),
% 1.36/0.53    inference(avatar_component_clause,[],[f402])).
% 1.36/0.53  fof(f430,plain,(
% 1.36/0.53    ~spl4_17 | spl4_21 | ~spl4_18),
% 1.36/0.53    inference(avatar_split_clause,[],[f425,f402,f427,f398])).
% 1.36/0.53  fof(f425,plain,(
% 1.36/0.53    r1_ordinal1(sK2,sK3(sK2)) | ~v3_ordinal1(sK3(sK2)) | ~spl4_18),
% 1.36/0.53    inference(subsumption_resolution,[],[f422,f46])).
% 1.36/0.53  fof(f422,plain,(
% 1.36/0.53    r1_ordinal1(sK2,sK3(sK2)) | ~v3_ordinal1(sK3(sK2)) | ~v3_ordinal1(sK2) | ~spl4_18),
% 1.36/0.53    inference(resolution,[],[f404,f78])).
% 1.36/0.53  fof(f421,plain,(
% 1.36/0.53    spl4_3 | spl4_17),
% 1.36/0.53    inference(avatar_contradiction_clause,[],[f420])).
% 1.36/0.53  fof(f420,plain,(
% 1.36/0.53    $false | (spl4_3 | spl4_17)),
% 1.36/0.53    inference(subsumption_resolution,[],[f419,f46])).
% 1.36/0.53  fof(f419,plain,(
% 1.36/0.53    ~v3_ordinal1(sK2) | (spl4_3 | spl4_17)),
% 1.36/0.53    inference(subsumption_resolution,[],[f418,f96])).
% 1.36/0.53  fof(f418,plain,(
% 1.36/0.53    v4_ordinal1(sK2) | ~v3_ordinal1(sK2) | spl4_17),
% 1.36/0.53    inference(resolution,[],[f400,f53])).
% 1.36/0.53  fof(f400,plain,(
% 1.36/0.53    ~v3_ordinal1(sK3(sK2)) | spl4_17),
% 1.36/0.53    inference(avatar_component_clause,[],[f398])).
% 1.36/0.53  fof(f405,plain,(
% 1.36/0.53    ~spl4_17 | spl4_18 | ~spl4_1 | ~spl4_15),
% 1.36/0.53    inference(avatar_split_clause,[],[f394,f377,f86,f402,f398])).
% 1.36/0.53  fof(f394,plain,(
% 1.36/0.53    r2_hidden(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2)))) | ~v3_ordinal1(sK3(sK2)) | (~spl4_1 | ~spl4_15)),
% 1.36/0.53    inference(resolution,[],[f379,f309])).
% 1.36/0.53  fof(f379,plain,(
% 1.36/0.53    r1_ordinal1(sK2,k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2)))) | ~spl4_15),
% 1.36/0.53    inference(avatar_component_clause,[],[f377])).
% 1.36/0.53  fof(f389,plain,(
% 1.36/0.53    spl4_3 | spl4_16),
% 1.36/0.53    inference(avatar_contradiction_clause,[],[f388])).
% 1.36/0.53  fof(f388,plain,(
% 1.36/0.53    $false | (spl4_3 | spl4_16)),
% 1.36/0.53    inference(subsumption_resolution,[],[f387,f46])).
% 1.36/0.53  fof(f387,plain,(
% 1.36/0.53    ~v3_ordinal1(sK2) | (spl4_3 | spl4_16)),
% 1.36/0.53    inference(subsumption_resolution,[],[f386,f96])).
% 1.36/0.53  fof(f386,plain,(
% 1.36/0.53    v4_ordinal1(sK2) | ~v3_ordinal1(sK2) | spl4_16),
% 1.36/0.53    inference(resolution,[],[f385,f53])).
% 1.36/0.53  fof(f385,plain,(
% 1.36/0.53    ~v3_ordinal1(sK3(sK2)) | spl4_16),
% 1.36/0.53    inference(resolution,[],[f383,f72])).
% 1.36/0.53  fof(f383,plain,(
% 1.36/0.53    ~v3_ordinal1(k2_xboole_0(sK3(sK2),k1_tarski(sK3(sK2)))) | spl4_16),
% 1.36/0.53    inference(avatar_component_clause,[],[f381])).
% 1.36/0.53  fof(f164,plain,(
% 1.36/0.53    ~spl4_2 | spl4_6),
% 1.36/0.53    inference(avatar_contradiction_clause,[],[f163])).
% 1.36/0.53  fof(f163,plain,(
% 1.36/0.53    $false | (~spl4_2 | spl4_6)),
% 1.36/0.53    inference(subsumption_resolution,[],[f162,f91])).
% 1.36/0.53  fof(f162,plain,(
% 1.36/0.53    ~sP0(sK2) | spl4_6),
% 1.36/0.53    inference(resolution,[],[f134,f43])).
% 1.36/0.53  fof(f43,plain,(
% 1.36/0.53    ( ! [X0] : (v3_ordinal1(sK1(X0)) | ~sP0(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f28])).
% 1.36/0.53  fof(f134,plain,(
% 1.36/0.53    ~v3_ordinal1(sK1(sK2)) | spl4_6),
% 1.36/0.53    inference(avatar_component_clause,[],[f132])).
% 1.36/0.53  fof(f97,plain,(
% 1.36/0.53    ~spl4_3 | spl4_2),
% 1.36/0.53    inference(avatar_split_clause,[],[f47,f89,f94])).
% 1.36/0.53  fof(f47,plain,(
% 1.36/0.53    sP0(sK2) | ~v4_ordinal1(sK2)),
% 1.36/0.53    inference(cnf_transformation,[],[f31])).
% 1.36/0.53  fof(f92,plain,(
% 1.36/0.53    spl4_1 | spl4_2),
% 1.36/0.53    inference(avatar_split_clause,[],[f70,f89,f86])).
% 1.36/0.53  fof(f70,plain,(
% 1.36/0.53    ( ! [X1] : (sP0(sK2) | sK2 != k2_xboole_0(X1,k1_tarski(X1)) | ~v3_ordinal1(X1)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f48,f50])).
% 1.36/0.53  fof(f48,plain,(
% 1.36/0.53    ( ! [X1] : (sP0(sK2) | k1_ordinal1(X1) != sK2 | ~v3_ordinal1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f31])).
% 1.36/0.53  % SZS output end Proof for theBenchmark
% 1.36/0.53  % (21915)------------------------------
% 1.36/0.53  % (21915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (21915)Termination reason: Refutation
% 1.36/0.53  
% 1.36/0.53  % (21915)Memory used [KB]: 10874
% 1.36/0.53  % (21915)Time elapsed: 0.124 s
% 1.36/0.53  % (21915)------------------------------
% 1.36/0.53  % (21915)------------------------------
% 1.36/0.53  % (21907)Success in time 0.179 s
%------------------------------------------------------------------------------
