%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:04 EST 2020

% Result     : Theorem 3.44s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 145 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  210 ( 709 expanded)
%              Number of equality atoms :   37 ( 110 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2026,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1971,f1974,f1980,f1982,f1983,f2014,f2024,f2025])).

fof(f2025,plain,
    ( ~ spl5_45
    | spl5_10 ),
    inference(avatar_split_clause,[],[f1847,f232,f1968])).

fof(f1968,plain,
    ( spl5_45
  <=> r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f232,plain,
    ( spl5_10
  <=> r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1847,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
    | spl5_10 ),
    inference(superposition,[],[f237,f65])).

fof(f65,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f39,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f237,plain,
    ( ! [X0] : ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,X0))
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f233,f70])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f233,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f232])).

fof(f2024,plain,
    ( spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f935,f232,f228])).

fof(f228,plain,
    ( spl5_9
  <=> r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f935,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f38,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f38,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f26])).

fof(f26,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2014,plain,
    ( spl5_46
    | spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f2013,f232,f228,f1976])).

fof(f1976,plain,
    ( spl5_46
  <=> r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f2013,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl5_9
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f2008,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f2008,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f234,f229,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f229,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f228])).

fof(f234,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f232])).

fof(f1983,plain,
    ( spl5_9
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f254,f1976,f228])).

fof(f254,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f38,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1982,plain,
    ( ~ spl5_9
    | ~ spl5_46 ),
    inference(avatar_contradiction_clause,[],[f1981])).

fof(f1981,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f1919,f1978])).

fof(f1978,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f1976])).

fof(f1919,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl5_9 ),
    inference(superposition,[],[f344,f47])).

fof(f344,plain,
    ( ! [X0] : ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f230,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f230,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f228])).

fof(f1980,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | spl5_46 ),
    inference(avatar_split_clause,[],[f319,f1976,f232,f228])).

fof(f319,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2] :
      ( k3_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),sK0)
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f38,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1974,plain,(
    spl5_44 ),
    inference(avatar_contradiction_clause,[],[f1972])).

fof(f1972,plain,
    ( $false
    | spl5_44 ),
    inference(unit_resulting_resolution,[],[f42,f1966])).

fof(f1966,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl5_44 ),
    inference(avatar_component_clause,[],[f1964])).

fof(f1964,plain,
    ( spl5_44
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1971,plain,
    ( ~ spl5_44
    | spl5_45
    | ~ spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f1959,f232,f228,f1968,f1964])).

fof(f1959,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl5_9
    | spl5_10 ),
    inference(superposition,[],[f345,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f345,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))
    | ~ spl5_9
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f233,f230,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:01:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (365)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (356)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (356)Refutation not found, incomplete strategy% (356)------------------------------
% 0.21/0.51  % (356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (356)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (356)Memory used [KB]: 1663
% 0.21/0.51  % (356)Time elapsed: 0.054 s
% 0.21/0.51  % (356)------------------------------
% 0.21/0.51  % (356)------------------------------
% 0.21/0.52  % (348)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (369)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (369)Refutation not found, incomplete strategy% (369)------------------------------
% 0.21/0.52  % (369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (369)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (369)Memory used [KB]: 6140
% 0.21/0.52  % (369)Time elapsed: 0.108 s
% 0.21/0.52  % (369)------------------------------
% 0.21/0.52  % (369)------------------------------
% 1.17/0.52  % (352)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.17/0.52  % (352)Refutation not found, incomplete strategy% (352)------------------------------
% 1.17/0.52  % (352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (352)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.52  
% 1.17/0.52  % (352)Memory used [KB]: 10746
% 1.17/0.52  % (352)Time elapsed: 0.109 s
% 1.17/0.52  % (352)------------------------------
% 1.17/0.52  % (352)------------------------------
% 1.17/0.53  % (355)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.17/0.53  % (343)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.17/0.53  % (344)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.17/0.53  % (361)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.17/0.53  % (342)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.17/0.53  % (343)Refutation not found, incomplete strategy% (343)------------------------------
% 1.17/0.53  % (343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.53  % (343)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.53  
% 1.17/0.53  % (343)Memory used [KB]: 1663
% 1.17/0.53  % (343)Time elapsed: 0.112 s
% 1.17/0.53  % (343)------------------------------
% 1.17/0.53  % (343)------------------------------
% 1.17/0.54  % (358)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.17/0.54  % (346)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.17/0.54  % (345)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.17/0.54  % (357)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.17/0.54  % (350)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.17/0.54  % (347)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.17/0.55  % (359)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.17/0.55  % (362)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.17/0.55  % (359)Refutation not found, incomplete strategy% (359)------------------------------
% 1.17/0.55  % (359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.55  % (359)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.55  
% 1.17/0.55  % (359)Memory used [KB]: 1663
% 1.17/0.55  % (359)Time elapsed: 0.128 s
% 1.17/0.55  % (359)------------------------------
% 1.17/0.55  % (359)------------------------------
% 1.17/0.55  % (351)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.17/0.55  % (354)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.17/0.55  % (349)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.17/0.55  % (367)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.55  % (370)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.44/0.55  % (354)Refutation not found, incomplete strategy% (354)------------------------------
% 1.44/0.55  % (354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (370)Refutation not found, incomplete strategy% (370)------------------------------
% 1.44/0.55  % (370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (370)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (370)Memory used [KB]: 10746
% 1.44/0.55  % (370)Time elapsed: 0.134 s
% 1.44/0.55  % (370)------------------------------
% 1.44/0.55  % (370)------------------------------
% 1.44/0.56  % (353)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.56  % (371)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.56  % (363)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.56  % (354)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (354)Memory used [KB]: 10618
% 1.44/0.56  % (354)Time elapsed: 0.141 s
% 1.44/0.56  % (354)------------------------------
% 1.44/0.56  % (354)------------------------------
% 1.44/0.56  % (368)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.44/0.56  % (358)Refutation not found, incomplete strategy% (358)------------------------------
% 1.44/0.56  % (358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (358)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (358)Memory used [KB]: 10618
% 1.44/0.56  % (358)Time elapsed: 0.147 s
% 1.44/0.56  % (358)------------------------------
% 1.44/0.56  % (358)------------------------------
% 1.44/0.56  % (368)Refutation not found, incomplete strategy% (368)------------------------------
% 1.44/0.56  % (368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (368)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (368)Memory used [KB]: 6140
% 1.44/0.56  % (368)Time elapsed: 0.148 s
% 1.44/0.56  % (368)------------------------------
% 1.44/0.56  % (368)------------------------------
% 1.44/0.57  % (366)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.44/0.57  % (366)Refutation not found, incomplete strategy% (366)------------------------------
% 1.44/0.57  % (366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (366)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (366)Memory used [KB]: 10618
% 1.44/0.57  % (366)Time elapsed: 0.150 s
% 1.44/0.57  % (366)------------------------------
% 1.44/0.57  % (366)------------------------------
% 1.44/0.57  % (364)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.44/0.57  % (360)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.44/0.58  % (360)Refutation not found, incomplete strategy% (360)------------------------------
% 1.44/0.58  % (360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.58  % (360)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.58  
% 1.44/0.58  % (360)Memory used [KB]: 1663
% 1.44/0.58  % (360)Time elapsed: 0.169 s
% 1.44/0.58  % (360)------------------------------
% 1.44/0.58  % (360)------------------------------
% 1.44/0.61  % (397)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.44/0.64  % (404)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.93/0.64  % (395)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.93/0.66  % (345)Refutation not found, incomplete strategy% (345)------------------------------
% 1.93/0.66  % (345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.67  % (345)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.67  
% 1.93/0.67  % (345)Memory used [KB]: 6140
% 1.93/0.67  % (345)Time elapsed: 0.247 s
% 1.93/0.67  % (345)------------------------------
% 1.93/0.67  % (345)------------------------------
% 1.93/0.67  % (400)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.93/0.67  % (415)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.93/0.67  % (420)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 1.93/0.67  % (415)Refutation not found, incomplete strategy% (415)------------------------------
% 1.93/0.67  % (415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.67  % (415)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.67  
% 1.93/0.67  % (415)Memory used [KB]: 10618
% 1.93/0.67  % (415)Time elapsed: 0.095 s
% 1.93/0.67  % (415)------------------------------
% 1.93/0.67  % (415)------------------------------
% 1.93/0.68  % (417)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.20/0.69  % (421)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.20/0.70  % (357)Refutation not found, incomplete strategy% (357)------------------------------
% 2.20/0.70  % (357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.70  % (357)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.70  
% 2.20/0.70  % (357)Memory used [KB]: 6140
% 2.20/0.70  % (357)Time elapsed: 0.249 s
% 2.20/0.70  % (357)------------------------------
% 2.20/0.70  % (357)------------------------------
% 2.20/0.71  % (424)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.20/0.71  % (424)Refutation not found, incomplete strategy% (424)------------------------------
% 2.20/0.71  % (424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.71  % (424)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.71  
% 2.20/0.71  % (424)Memory used [KB]: 10746
% 2.20/0.71  % (424)Time elapsed: 0.108 s
% 2.20/0.71  % (424)------------------------------
% 2.20/0.71  % (424)------------------------------
% 2.20/0.71  % (422)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.20/0.73  % (430)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.55/0.78  % (479)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.81/0.82  % (480)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.81/0.82  % (344)Time limit reached!
% 2.81/0.82  % (344)------------------------------
% 2.81/0.82  % (344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.82  % (344)Termination reason: Time limit
% 2.81/0.82  
% 2.81/0.82  % (344)Memory used [KB]: 6524
% 2.81/0.82  % (344)Time elapsed: 0.404 s
% 2.81/0.82  % (344)------------------------------
% 2.81/0.82  % (344)------------------------------
% 2.81/0.84  % (520)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.97/0.87  % (520)Refutation not found, incomplete strategy% (520)------------------------------
% 2.97/0.87  % (520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.97/0.87  % (520)Termination reason: Refutation not found, incomplete strategy
% 2.97/0.87  
% 2.97/0.87  % (520)Memory used [KB]: 10618
% 2.97/0.87  % (520)Time elapsed: 0.133 s
% 2.97/0.87  % (520)------------------------------
% 2.97/0.87  % (520)------------------------------
% 2.97/0.87  % (529)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.44/0.94  % (479)Refutation found. Thanks to Tanya!
% 3.44/0.94  % SZS status Theorem for theBenchmark
% 3.44/0.94  % SZS output start Proof for theBenchmark
% 3.44/0.94  fof(f2026,plain,(
% 3.44/0.94    $false),
% 3.44/0.94    inference(avatar_sat_refutation,[],[f1971,f1974,f1980,f1982,f1983,f2014,f2024,f2025])).
% 3.44/0.94  fof(f2025,plain,(
% 3.44/0.94    ~spl5_45 | spl5_10),
% 3.44/0.94    inference(avatar_split_clause,[],[f1847,f232,f1968])).
% 3.44/0.94  fof(f1968,plain,(
% 3.44/0.94    spl5_45 <=> r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)),
% 3.44/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 3.44/0.94  fof(f232,plain,(
% 3.44/0.94    spl5_10 <=> r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 3.44/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.44/0.94  fof(f1847,plain,(
% 3.44/0.94    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | spl5_10),
% 3.44/0.94    inference(superposition,[],[f237,f65])).
% 3.44/0.94  fof(f65,plain,(
% 3.44/0.94    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.44/0.94    inference(definition_unfolding,[],[f44,f39])).
% 3.44/0.94  fof(f39,plain,(
% 3.44/0.94    k1_xboole_0 = o_0_0_xboole_0),
% 3.44/0.94    inference(cnf_transformation,[],[f3])).
% 3.44/0.94  fof(f3,axiom,(
% 3.44/0.94    k1_xboole_0 = o_0_0_xboole_0),
% 3.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 3.44/0.94  fof(f44,plain,(
% 3.44/0.94    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.44/0.94    inference(cnf_transformation,[],[f15])).
% 3.44/0.94  fof(f15,axiom,(
% 3.44/0.94    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 3.44/0.94  fof(f237,plain,(
% 3.44/0.94    ( ! [X0] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,X0))) ) | spl5_10),
% 3.44/0.94    inference(unit_resulting_resolution,[],[f233,f70])).
% 3.44/0.94  fof(f70,plain,(
% 3.44/0.94    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.44/0.94    inference(equality_resolution,[],[f58])).
% 3.44/0.94  fof(f58,plain,(
% 3.44/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.44/0.94    inference(cnf_transformation,[],[f37])).
% 3.44/0.94  fof(f37,plain,(
% 3.44/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.44/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 3.44/0.94  fof(f36,plain,(
% 3.44/0.94    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.44/0.94    introduced(choice_axiom,[])).
% 3.44/0.94  fof(f35,plain,(
% 3.44/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.44/0.94    inference(rectify,[],[f34])).
% 3.44/0.94  fof(f34,plain,(
% 3.44/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.44/0.94    inference(flattening,[],[f33])).
% 3.44/0.94  fof(f33,plain,(
% 3.44/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.44/0.94    inference(nnf_transformation,[],[f4])).
% 3.44/0.94  fof(f4,axiom,(
% 3.44/0.94    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.44/0.94  fof(f233,plain,(
% 3.44/0.94    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | spl5_10),
% 3.44/0.94    inference(avatar_component_clause,[],[f232])).
% 3.44/0.94  fof(f2024,plain,(
% 3.44/0.94    spl5_9 | spl5_10),
% 3.44/0.94    inference(avatar_split_clause,[],[f935,f232,f228])).
% 3.44/0.94  fof(f228,plain,(
% 3.44/0.94    spl5_9 <=> r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 3.44/0.94    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.44/0.94  fof(f935,plain,(
% 3.44/0.94    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 3.44/0.94    inference(equality_resolution,[],[f77])).
% 3.44/0.94  fof(f77,plain,(
% 3.44/0.94    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 3.44/0.94    inference(superposition,[],[f38,f61])).
% 3.44/0.94  fof(f61,plain,(
% 3.44/0.94    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.44/0.94    inference(cnf_transformation,[],[f37])).
% 3.44/0.94  fof(f38,plain,(
% 3.44/0.94    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 3.44/0.94    inference(cnf_transformation,[],[f27])).
% 3.44/0.94  fof(f27,plain,(
% 3.44/0.94    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 3.44/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f26])).
% 3.44/0.94  fof(f26,plain,(
% 3.44/0.94    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 3.44/0.94    introduced(choice_axiom,[])).
% 3.44/0.94  fof(f22,plain,(
% 3.44/0.94    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.44/0.94    inference(ennf_transformation,[],[f18])).
% 3.44/0.94  fof(f18,negated_conjecture,(
% 3.44/0.94    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.44/0.94    inference(negated_conjecture,[],[f17])).
% 3.44/0.94  fof(f17,conjecture,(
% 3.44/0.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.44/0.95  fof(f2014,plain,(
% 3.44/0.95    spl5_46 | spl5_9 | ~spl5_10),
% 3.44/0.95    inference(avatar_split_clause,[],[f2013,f232,f228,f1976])).
% 3.44/0.95  fof(f1976,plain,(
% 3.44/0.95    spl5_46 <=> r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 3.44/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 3.44/0.95  fof(f2013,plain,(
% 3.44/0.95    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (spl5_9 | ~spl5_10)),
% 3.44/0.95    inference(forward_demodulation,[],[f2008,f47])).
% 3.44/0.95  fof(f47,plain,(
% 3.44/0.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.44/0.95    inference(cnf_transformation,[],[f16])).
% 3.44/0.95  fof(f16,axiom,(
% 3.44/0.95    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.44/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 3.44/0.95  fof(f2008,plain,(
% 3.44/0.95    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (spl5_9 | ~spl5_10)),
% 3.44/0.95    inference(unit_resulting_resolution,[],[f234,f229,f68])).
% 3.44/0.95  fof(f68,plain,(
% 3.44/0.95    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.44/0.95    inference(equality_resolution,[],[f60])).
% 3.44/0.95  fof(f60,plain,(
% 3.44/0.95    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.44/0.95    inference(cnf_transformation,[],[f37])).
% 3.44/0.95  fof(f229,plain,(
% 3.44/0.95    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl5_9),
% 3.44/0.95    inference(avatar_component_clause,[],[f228])).
% 3.44/0.95  fof(f234,plain,(
% 3.44/0.95    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl5_10),
% 3.44/0.95    inference(avatar_component_clause,[],[f232])).
% 3.44/0.95  fof(f1983,plain,(
% 3.44/0.95    spl5_9 | ~spl5_46),
% 3.44/0.95    inference(avatar_split_clause,[],[f254,f1976,f228])).
% 3.44/0.95  fof(f254,plain,(
% 3.44/0.95    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 3.44/0.95    inference(equality_resolution,[],[f78])).
% 3.44/0.95  fof(f78,plain,(
% 3.44/0.95    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 3.44/0.95    inference(superposition,[],[f38,f62])).
% 3.44/0.95  fof(f62,plain,(
% 3.44/0.95    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.44/0.95    inference(cnf_transformation,[],[f37])).
% 3.44/0.95  fof(f1982,plain,(
% 3.44/0.95    ~spl5_9 | ~spl5_46),
% 3.44/0.95    inference(avatar_contradiction_clause,[],[f1981])).
% 3.44/0.95  fof(f1981,plain,(
% 3.44/0.95    $false | (~spl5_9 | ~spl5_46)),
% 3.44/0.95    inference(subsumption_resolution,[],[f1919,f1978])).
% 3.44/0.95  fof(f1978,plain,(
% 3.44/0.95    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl5_46),
% 3.44/0.95    inference(avatar_component_clause,[],[f1976])).
% 3.44/0.95  fof(f1919,plain,(
% 3.44/0.95    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl5_9),
% 3.44/0.95    inference(superposition,[],[f344,f47])).
% 3.44/0.95  fof(f344,plain,(
% 3.44/0.95    ( ! [X0] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))) ) | ~spl5_9),
% 3.44/0.95    inference(unit_resulting_resolution,[],[f230,f69])).
% 3.44/0.95  fof(f69,plain,(
% 3.44/0.95    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.44/0.95    inference(equality_resolution,[],[f59])).
% 3.44/0.95  fof(f59,plain,(
% 3.44/0.95    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.44/0.95    inference(cnf_transformation,[],[f37])).
% 3.44/0.95  fof(f230,plain,(
% 3.44/0.95    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl5_9),
% 3.44/0.95    inference(avatar_component_clause,[],[f228])).
% 3.44/0.95  fof(f1980,plain,(
% 3.44/0.95    ~spl5_9 | ~spl5_10 | spl5_46),
% 3.44/0.95    inference(avatar_split_clause,[],[f319,f1976,f232,f228])).
% 3.44/0.95  fof(f319,plain,(
% 3.44/0.95    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 3.44/0.95    inference(equality_resolution,[],[f79])).
% 3.44/0.95  fof(f79,plain,(
% 3.44/0.95    ( ! [X2] : (k3_xboole_0(sK0,sK1) != X2 | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),sK0) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),X2)) )),
% 3.44/0.95    inference(superposition,[],[f38,f63])).
% 3.44/0.95  fof(f63,plain,(
% 3.44/0.95    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.44/0.95    inference(cnf_transformation,[],[f37])).
% 3.44/0.95  fof(f1974,plain,(
% 3.44/0.95    spl5_44),
% 3.44/0.95    inference(avatar_contradiction_clause,[],[f1972])).
% 3.44/0.95  fof(f1972,plain,(
% 3.44/0.95    $false | spl5_44),
% 3.44/0.95    inference(unit_resulting_resolution,[],[f42,f1966])).
% 3.44/0.95  fof(f1966,plain,(
% 3.44/0.95    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl5_44),
% 3.44/0.95    inference(avatar_component_clause,[],[f1964])).
% 3.44/0.95  fof(f1964,plain,(
% 3.44/0.95    spl5_44 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 3.44/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 3.44/0.95  fof(f42,plain,(
% 3.44/0.95    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.44/0.95    inference(cnf_transformation,[],[f10])).
% 3.44/0.95  fof(f10,axiom,(
% 3.44/0.95    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.44/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.44/0.95  fof(f1971,plain,(
% 3.44/0.95    ~spl5_44 | spl5_45 | ~spl5_9 | spl5_10),
% 3.44/0.95    inference(avatar_split_clause,[],[f1959,f232,f228,f1968,f1964])).
% 3.44/0.95  fof(f1959,plain,(
% 3.44/0.95    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl5_9 | spl5_10)),
% 3.44/0.95    inference(superposition,[],[f345,f66])).
% 3.44/0.95  fof(f66,plain,(
% 3.44/0.95    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.44/0.95    inference(definition_unfolding,[],[f55,f39])).
% 3.44/0.95  fof(f55,plain,(
% 3.44/0.95    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.44/0.95    inference(cnf_transformation,[],[f32])).
% 3.44/0.95  fof(f32,plain,(
% 3.44/0.95    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.44/0.95    inference(nnf_transformation,[],[f8])).
% 3.44/0.95  fof(f8,axiom,(
% 3.44/0.95    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.44/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.44/0.95  fof(f345,plain,(
% 3.44/0.95    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) | (~spl5_9 | spl5_10)),
% 3.44/0.95    inference(unit_resulting_resolution,[],[f233,f230,f68])).
% 3.44/0.95  % SZS output end Proof for theBenchmark
% 3.44/0.95  % (479)------------------------------
% 3.44/0.95  % (479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.44/0.95  % (479)Termination reason: Refutation
% 3.44/0.95  
% 3.44/0.95  % (479)Memory used [KB]: 11769
% 3.44/0.95  % (479)Time elapsed: 0.216 s
% 3.44/0.95  % (479)------------------------------
% 3.44/0.95  % (479)------------------------------
% 3.44/0.95  % (341)Success in time 0.575 s
%------------------------------------------------------------------------------
