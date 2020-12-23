%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 196 expanded)
%              Number of leaves         :   33 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  322 ( 530 expanded)
%              Number of equality atoms :   43 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f965,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f85,f91,f162,f260,f418,f633,f649,f711,f721,f724,f899,f962,f964])).

fof(f964,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f962,plain,
    ( ~ spl7_3
    | ~ spl7_68 ),
    inference(avatar_contradiction_clause,[],[f961])).

fof(f961,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f948,f98])).

fof(f98,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f78,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f78,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl7_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f948,plain,
    ( r2_hidden(k4_tarski(sK1(k1_relat_1(k1_xboole_0)),sK5(k1_xboole_0,sK1(k1_relat_1(k1_xboole_0)))),k1_xboole_0)
    | ~ spl7_68 ),
    inference(unit_resulting_resolution,[],[f63,f720,f55])).

fof(f55,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f720,plain,
    ( r2_hidden(sK1(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f718])).

fof(f718,plain,
    ( spl7_68
  <=> r2_hidden(sK1(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f63,plain,(
    ! [X0] : sP0(X0,k1_relat_1(X0)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f8,f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f899,plain,
    ( spl7_81
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f898,f257,f88,f82,f888])).

fof(f888,plain,
    ( spl7_81
  <=> r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f82,plain,
    ( spl7_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f88,plain,
    ( spl7_5
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f257,plain,
    ( spl7_29
  <=> k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f898,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_29 ),
    inference(forward_demodulation,[],[f870,f259])).

fof(f259,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f257])).

fof(f870,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(k4_relat_1(k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f90,f84,f41,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f84,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f90,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f724,plain,
    ( ~ spl7_63
    | spl7_1
    | ~ spl7_61 ),
    inference(avatar_split_clause,[],[f665,f646,f67,f675])).

fof(f675,plain,
    ( spl7_63
  <=> r1_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f67,plain,
    ( spl7_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f646,plain,
    ( spl7_61
  <=> k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f665,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ r1_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl7_61 ),
    inference(superposition,[],[f648,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f648,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f646])).

fof(f721,plain,
    ( spl7_68
    | spl7_65 ),
    inference(avatar_split_clause,[],[f715,f695,f718])).

fof(f695,plain,
    ( spl7_65
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f715,plain,
    ( r2_hidden(sK1(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))
    | spl7_65 ),
    inference(unit_resulting_resolution,[],[f697,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f697,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | spl7_65 ),
    inference(avatar_component_clause,[],[f695])).

fof(f711,plain,
    ( ~ spl7_65
    | spl7_63 ),
    inference(avatar_split_clause,[],[f687,f675,f695])).

fof(f687,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | spl7_63 ),
    inference(resolution,[],[f677,f360])).

fof(f360,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f50,f48])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f677,plain,
    ( ~ r1_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | spl7_63 ),
    inference(avatar_component_clause,[],[f675])).

fof(f649,plain,
    ( spl7_61
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f643,f622,f646])).

fof(f622,plain,
    ( spl7_60
  <=> r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f643,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl7_60 ),
    inference(unit_resulting_resolution,[],[f624,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f624,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f622])).

fof(f633,plain,
    ( spl7_60
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f632,f159,f88,f82,f622])).

fof(f159,plain,
    ( spl7_15
  <=> k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f632,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f598,f161])).

fof(f161,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f598,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f90,f84,f41,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f418,plain,
    ( ~ spl7_46
    | spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f410,f76,f71,f415])).

fof(f415,plain,
    ( spl7_46
  <=> r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f71,plain,
    ( spl7_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f410,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | spl7_2
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f73,f400])).

fof(f400,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,k1_xboole_0)
        | k1_xboole_0 = X4 )
    | ~ spl7_3 ),
    inference(superposition,[],[f62,f380])).

fof(f380,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f375,f53])).

fof(f375,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f98,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f260,plain,
    ( spl7_29
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f218,f82,f257])).

fof(f218,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f84,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f162,plain,
    ( spl7_15
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f130,f82,f159])).

fof(f130,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f84,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,
    ( spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f86,f82,f88])).

fof(f86,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f84,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f85,plain,
    ( spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f80,f76,f82])).

fof(f80,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f78,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f79,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f40,f76])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f74,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f39,f71,f67])).

fof(f39,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (21281)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.44  % (21278)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.44  % (21278)Refutation not found, incomplete strategy% (21278)------------------------------
% 0.21/0.44  % (21278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (21278)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (21278)Memory used [KB]: 10490
% 0.21/0.44  % (21278)Time elapsed: 0.045 s
% 0.21/0.44  % (21278)------------------------------
% 0.21/0.44  % (21278)------------------------------
% 0.21/0.44  % (21291)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.45  % (21284)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.45  % (21283)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (21292)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (21275)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (21275)Refutation not found, incomplete strategy% (21275)------------------------------
% 0.21/0.47  % (21275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (21275)Memory used [KB]: 6140
% 0.21/0.47  % (21275)Time elapsed: 0.068 s
% 0.21/0.47  % (21275)------------------------------
% 0.21/0.47  % (21275)------------------------------
% 0.21/0.47  % (21279)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (21277)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (21279)Refutation not found, incomplete strategy% (21279)------------------------------
% 0.21/0.47  % (21279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21279)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (21279)Memory used [KB]: 1663
% 0.21/0.47  % (21279)Time elapsed: 0.074 s
% 0.21/0.47  % (21279)------------------------------
% 0.21/0.47  % (21279)------------------------------
% 0.21/0.47  % (21289)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (21295)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (21295)Refutation not found, incomplete strategy% (21295)------------------------------
% 0.21/0.48  % (21295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21295)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21295)Memory used [KB]: 10618
% 0.21/0.48  % (21295)Time elapsed: 0.078 s
% 0.21/0.48  % (21295)------------------------------
% 0.21/0.48  % (21295)------------------------------
% 0.21/0.48  % (21276)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (21276)Refutation not found, incomplete strategy% (21276)------------------------------
% 0.21/0.48  % (21276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21276)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21276)Memory used [KB]: 10618
% 0.21/0.48  % (21276)Time elapsed: 0.083 s
% 0.21/0.48  % (21276)------------------------------
% 0.21/0.48  % (21276)------------------------------
% 0.21/0.48  % (21290)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (21280)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (21290)Refutation not found, incomplete strategy% (21290)------------------------------
% 0.21/0.48  % (21290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21290)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21290)Memory used [KB]: 6140
% 0.21/0.48  % (21290)Time elapsed: 0.070 s
% 0.21/0.48  % (21290)------------------------------
% 0.21/0.48  % (21290)------------------------------
% 0.21/0.48  % (21285)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (21285)Refutation not found, incomplete strategy% (21285)------------------------------
% 0.21/0.48  % (21285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21285)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21285)Memory used [KB]: 6012
% 0.21/0.48  % (21285)Time elapsed: 0.073 s
% 0.21/0.48  % (21285)------------------------------
% 0.21/0.48  % (21285)------------------------------
% 0.21/0.48  % (21287)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (21287)Refutation not found, incomplete strategy% (21287)------------------------------
% 0.21/0.48  % (21287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21287)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21287)Memory used [KB]: 6012
% 0.21/0.48  % (21287)Time elapsed: 0.002 s
% 0.21/0.48  % (21287)------------------------------
% 0.21/0.48  % (21287)------------------------------
% 0.21/0.48  % (21288)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (21288)Refutation not found, incomplete strategy% (21288)------------------------------
% 0.21/0.49  % (21288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21288)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (21288)Memory used [KB]: 1535
% 0.21/0.49  % (21288)Time elapsed: 0.078 s
% 0.21/0.49  % (21288)------------------------------
% 0.21/0.49  % (21288)------------------------------
% 0.21/0.49  % (21282)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (21291)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f965,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f74,f79,f85,f91,f162,f260,f418,f633,f649,f711,f721,f724,f899,f962,f964])).
% 0.21/0.49  fof(f964,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relat_1(k1_xboole_0) | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f962,plain,(
% 0.21/0.49    ~spl7_3 | ~spl7_68),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f961])).
% 0.21/0.49  fof(f961,plain,(
% 0.21/0.49    $false | (~spl7_3 | ~spl7_68)),
% 0.21/0.49    inference(subsumption_resolution,[],[f948,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f78,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(rectify,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl7_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl7_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.49  fof(f948,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK1(k1_relat_1(k1_xboole_0)),sK5(k1_xboole_0,sK1(k1_relat_1(k1_xboole_0)))),k1_xboole_0) | ~spl7_68),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f63,f720,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | ~sP0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f35,f34,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f720,plain,(
% 0.21/0.49    r2_hidden(sK1(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) | ~spl7_68),
% 0.21/0.49    inference(avatar_component_clause,[],[f718])).
% 0.21/0.49  fof(f718,plain,(
% 0.21/0.49    spl7_68 <=> r2_hidden(sK1(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(X0,k1_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sP0(X0,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> sP0(X0,X1))),
% 0.21/0.49    inference(definition_folding,[],[f8,f22])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.49  fof(f899,plain,(
% 0.21/0.49    spl7_81 | ~spl7_4 | ~spl7_5 | ~spl7_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f898,f257,f88,f82,f888])).
% 0.21/0.49  fof(f888,plain,(
% 0.21/0.49    spl7_81 <=> r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl7_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl7_5 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    spl7_29 <=> k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.49  fof(f898,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) | (~spl7_4 | ~spl7_5 | ~spl7_29)),
% 0.21/0.49    inference(forward_demodulation,[],[f870,f259])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) | ~spl7_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f257])).
% 0.21/0.49  fof(f870,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(k4_relat_1(k1_xboole_0))) | (~spl7_4 | ~spl7_5)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f90,f84,f41,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | ~spl7_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl7_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f88])).
% 0.21/0.49  fof(f724,plain,(
% 0.21/0.49    ~spl7_63 | spl7_1 | ~spl7_61),
% 0.21/0.49    inference(avatar_split_clause,[],[f665,f646,f67,f675])).
% 0.21/0.49  fof(f675,plain,(
% 0.21/0.49    spl7_63 <=> r1_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl7_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f646,plain,(
% 0.21/0.49    spl7_61 <=> k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 0.21/0.49  fof(f665,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~r1_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~spl7_61),
% 0.21/0.49    inference(superposition,[],[f648,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.49  fof(f648,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~spl7_61),
% 0.21/0.49    inference(avatar_component_clause,[],[f646])).
% 0.21/0.49  fof(f721,plain,(
% 0.21/0.49    spl7_68 | spl7_65),
% 0.21/0.49    inference(avatar_split_clause,[],[f715,f695,f718])).
% 0.21/0.49  fof(f695,plain,(
% 0.21/0.49    spl7_65 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).
% 0.21/0.49  fof(f715,plain,(
% 0.21/0.49    r2_hidden(sK1(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) | spl7_65),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f697,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f697,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | spl7_65),
% 0.21/0.49    inference(avatar_component_clause,[],[f695])).
% 0.21/0.49  fof(f711,plain,(
% 0.21/0.49    ~spl7_65 | spl7_63),
% 0.21/0.49    inference(avatar_split_clause,[],[f687,f675,f695])).
% 0.21/0.49  fof(f687,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | spl7_63),
% 0.21/0.49    inference(resolution,[],[f677,f360])).
% 0.21/0.49  fof(f360,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(resolution,[],[f50,f48])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.49  fof(f677,plain,(
% 0.21/0.49    ~r1_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | spl7_63),
% 0.21/0.49    inference(avatar_component_clause,[],[f675])).
% 0.21/0.49  fof(f649,plain,(
% 0.21/0.49    spl7_61 | ~spl7_60),
% 0.21/0.49    inference(avatar_split_clause,[],[f643,f622,f646])).
% 0.21/0.49  fof(f622,plain,(
% 0.21/0.49    spl7_60 <=> r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 0.21/0.49  fof(f643,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~spl7_60),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f624,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.49  fof(f624,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~spl7_60),
% 0.21/0.49    inference(avatar_component_clause,[],[f622])).
% 0.21/0.49  fof(f633,plain,(
% 0.21/0.49    spl7_60 | ~spl7_4 | ~spl7_5 | ~spl7_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f632,f159,f88,f82,f622])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    spl7_15 <=> k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.49  fof(f632,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | (~spl7_4 | ~spl7_5 | ~spl7_15)),
% 0.21/0.49    inference(forward_demodulation,[],[f598,f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl7_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f159])).
% 0.21/0.49  fof(f598,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(k1_xboole_0))) | (~spl7_4 | ~spl7_5)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f90,f84,f41,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f418,plain,(
% 0.21/0.49    ~spl7_46 | spl7_2 | ~spl7_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f410,f76,f71,f415])).
% 0.21/0.49  fof(f415,plain,(
% 0.21/0.49    spl7_46 <=> r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl7_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f410,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | (spl7_2 | ~spl7_3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f73,f400])).
% 0.21/0.49  fof(f400,plain,(
% 0.21/0.49    ( ! [X4] : (~r1_tarski(X4,k1_xboole_0) | k1_xboole_0 = X4) ) | ~spl7_3),
% 0.21/0.49    inference(superposition,[],[f62,f380])).
% 0.21/0.49  fof(f380,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl7_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f375,f53])).
% 0.21/0.49  fof(f375,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl7_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f98,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    spl7_29 | ~spl7_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f218,f82,f257])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) | ~spl7_4),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f84,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl7_15 | ~spl7_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f130,f82,f159])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl7_4),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f84,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl7_5 | ~spl7_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f86,f82,f88])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl7_4),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f84,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl7_4 | ~spl7_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f80,f76,f82])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | ~spl7_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f78,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl7_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f76])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~spl7_1 | ~spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f71,f67])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (21291)------------------------------
% 0.21/0.49  % (21291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21291)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (21291)Memory used [KB]: 11129
% 0.21/0.49  % (21291)Time elapsed: 0.081 s
% 0.21/0.49  % (21291)------------------------------
% 0.21/0.49  % (21291)------------------------------
% 0.21/0.49  % (21274)Success in time 0.128 s
%------------------------------------------------------------------------------
