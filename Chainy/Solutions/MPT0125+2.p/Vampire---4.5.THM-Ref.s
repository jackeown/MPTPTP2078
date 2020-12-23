%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0125+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:11 EST 2020

% Result     : Theorem 7.03s
% Output     : Refutation 7.03s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 135 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  301 ( 757 expanded)
%              Number of equality atoms :  124 ( 340 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3941,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f565,f601,f659,f3172,f3173,f3940])).

fof(f3940,plain,(
    ~ spl12_5 ),
    inference(avatar_contradiction_clause,[],[f3939])).

fof(f3939,plain,
    ( $false
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f3938,f289])).

fof(f289,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f288])).

fof(f288,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f239])).

fof(f239,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f195,f196])).

fof(f196,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f195,plain,(
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
    inference(rectify,[],[f194])).

fof(f194,plain,(
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
    inference(nnf_transformation,[],[f174])).

fof(f174,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f3938,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f3937,f231])).

fof(f231,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f193])).

fof(f193,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f183,f192])).

fof(f192,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(choice_axiom,[])).

fof(f183,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(ennf_transformation,[],[f179])).

fof(f179,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(negated_conjecture,[],[f178])).

fof(f178,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f3937,plain,
    ( k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f3928,f292])).

fof(f292,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f291])).

fof(f291,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f244])).

fof(f244,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f202])).

fof(f202,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f200,f201])).

fof(f201,plain,(
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

fof(f200,plain,(
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
    inference(rectify,[],[f199])).

fof(f199,plain,(
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
    inference(flattening,[],[f198])).

fof(f198,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f3928,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl12_5 ),
    inference(superposition,[],[f262,f564])).

fof(f564,plain,
    ( sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f562])).

fof(f562,plain,
    ( spl12_5
  <=> sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f262,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f208])).

fof(f208,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f206,f207])).

fof(f207,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f206,plain,(
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
    inference(rectify,[],[f205])).

fof(f205,plain,(
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
    inference(flattening,[],[f204])).

fof(f204,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f3173,plain,
    ( spl12_1
    | spl12_2
    | spl12_3 ),
    inference(avatar_split_clause,[],[f504,f461,f435,f431])).

fof(f431,plain,
    ( spl12_1
  <=> r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f435,plain,
    ( spl12_2
  <=> r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f461,plain,
    ( spl12_3
  <=> r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f504,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK1))
    | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK0))
    | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(equality_resolution,[],[f309])).

fof(f309,plain,(
    ! [X0] :
      ( k2_tarski(sK0,sK1) != X0
      | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X0),k1_tarski(sK1))
      | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X0),k1_tarski(sK0))
      | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X0),X0) ) ),
    inference(superposition,[],[f231,f260])).

fof(f260,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f208])).

fof(f3172,plain,(
    ~ spl12_4 ),
    inference(avatar_contradiction_clause,[],[f3171])).

fof(f3171,plain,
    ( $false
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f3170,f289])).

fof(f3170,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f3169,f231])).

fof(f3169,plain,
    ( k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f3156,f294])).

fof(f294,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f293])).

fof(f293,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f243])).

fof(f243,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f202])).

fof(f3156,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl12_4 ),
    inference(superposition,[],[f261,f560])).

fof(f560,plain,
    ( sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f558])).

fof(f558,plain,
    ( spl12_4
  <=> sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f261,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f208])).

fof(f659,plain,
    ( spl12_5
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f635,f461,f562])).

fof(f635,plain,
    ( sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))
    | ~ spl12_3 ),
    inference(resolution,[],[f463,f290])).

fof(f290,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f238])).

fof(f238,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f197])).

fof(f463,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK1))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f461])).

fof(f601,plain,
    ( spl12_4
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f577,f435,f558])).

fof(f577,plain,
    ( sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))
    | ~ spl12_2 ),
    inference(resolution,[],[f436,f290])).

fof(f436,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK0))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f435])).

fof(f565,plain,
    ( spl12_4
    | spl12_5
    | ~ spl12_1 ),
    inference(avatar_split_clause,[],[f533,f431,f562,f558])).

fof(f533,plain,
    ( sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))
    | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))
    | ~ spl12_1 ),
    inference(resolution,[],[f432,f295])).

fof(f295,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f242])).

fof(f242,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f202])).

fof(f432,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f431])).
%------------------------------------------------------------------------------
