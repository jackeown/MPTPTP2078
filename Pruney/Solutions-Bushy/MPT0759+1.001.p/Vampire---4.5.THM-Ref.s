%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0759+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 124 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  218 ( 556 expanded)
%              Number of equality atoms :   65 ( 160 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f595,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f439,f443,f466,f594])).

fof(f594,plain,(
    ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f592,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f592,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f591,f40])).

fof(f40,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f591,plain,
    ( r2_hidden(sK0,sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f580,f48])).

fof(f48,plain,(
    sK0 != k4_xboole_0(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f23,plain,(
    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).

fof(f10,plain,
    ( ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0
   => sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_ordinal1)).

fof(f580,plain,
    ( r2_hidden(sK0,sK0)
    | sK0 = k4_xboole_0(k1_ordinal1(sK0),k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl3_25 ),
    inference(superposition,[],[f36,f438])).

fof(f438,plain,
    ( sK0 = sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl3_25
  <=> sK0 = sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f466,plain,
    ( spl3_25
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f458,f217,f436])).

fof(f217,plain,
    ( spl3_13
  <=> r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f458,plain,
    ( sK0 = sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0)
    | ~ spl3_13 ),
    inference(resolution,[],[f218,f41])).

fof(f41,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f218,plain,
    ( r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f217])).

fof(f443,plain,
    ( ~ spl3_12
    | spl3_13 ),
    inference(avatar_split_clause,[],[f442,f217,f213])).

fof(f213,plain,
    ( spl3_12
  <=> r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f442,plain,
    ( r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f264,f195])).

fof(f195,plain,(
    r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f194,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f194,plain,
    ( r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_ordinal1(sK0))
    | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( sK0 != X0
      | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),X0),k1_ordinal1(sK0))
      | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),X0),X0) ) ),
    inference(superposition,[],[f48,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f264,plain,
    ( r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_ordinal1(sK0))
    | ~ r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2] :
      ( sK0 != X2
      | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),X2),k1_tarski(sK0))
      | ~ r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),X2),k1_ordinal1(sK0))
      | ~ r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),X2),X2) ) ),
    inference(superposition,[],[f48,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f439,plain,
    ( spl3_12
    | spl3_25 ),
    inference(avatar_split_clause,[],[f369,f436,f213])).

fof(f369,plain,
    ( sK0 = sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0)
    | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),sK0) ),
    inference(resolution,[],[f195,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
