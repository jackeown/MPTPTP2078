%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 192 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  280 ( 807 expanded)
%              Number of equality atoms :   26 ( 126 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f874,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f73,f337,f873])).

fof(f873,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f872])).

fof(f872,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f339,f870])).

fof(f870,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | ~ spl7_1
    | spl7_2 ),
    inference(superposition,[],[f852,f160])).

fof(f160,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f42,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f852,plain,
    ( ! [X0] : ~ r2_hidden(sK4(k2_relat_1(sK1),sK0),k9_relat_1(sK1,X0))
    | ~ spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f45,f340,f339,f846])).

fof(f846,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,k1_xboole_0)
        | ~ r2_hidden(X3,k9_relat_1(sK1,X2))
        | ~ r2_hidden(X3,k2_relat_1(sK1))
        | ~ r2_hidden(X3,sK0) )
    | ~ spl7_1 ),
    inference(superposition,[],[f762,f66])).

fof(f66,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl7_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f762,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X2,k10_relat_1(sK1,X1))
      | ~ r2_hidden(X0,k9_relat_1(sK1,X2))
      | ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f756])).

fof(f756,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X2))
      | ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ r2_hidden(X0,k9_relat_1(sK1,X2))
      | ~ r1_xboole_0(X2,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f526,f226])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,sK1),X2)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f210,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f210,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,sK1),X1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f526,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,sK1),k10_relat_1(sK1,X2))
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(global_subsumption,[],[f42,f521])).

fof(f521,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | ~ r2_hidden(X0,X2)
      | r2_hidden(sK5(X0,X1,sK1),k10_relat_1(sK1,X2))
      | ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f370,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
            & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
        & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f370,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,sK1),X0),sK1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f57,f42])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f340,plain,
    ( r2_hidden(sK4(k2_relat_1(sK1),sK0),sK0)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f71,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f339,plain,
    ( r2_hidden(sK4(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f71,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f337,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f285,f334])).

fof(f334,plain,
    ( r2_hidden(sK6(sK2(k10_relat_1(sK1,sK0)),sK0,sK1),k2_relat_1(sK1))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f42,f82,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,
    ( r2_hidden(sK2(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f67,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f67,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f285,plain,
    ( ~ r2_hidden(sK6(sK2(k10_relat_1(sK1,sK0)),sK0,sK1),k2_relat_1(sK1))
    | spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f75,f258,f52])).

fof(f258,plain,
    ( r2_hidden(sK6(sK2(k10_relat_1(sK1,sK0)),sK0,sK1),sK0)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f42,f82,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,
    ( r1_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f70,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f70,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f73,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f43,f69,f65])).

fof(f43,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f44,f69,f65])).

fof(f44,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:44:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (22201)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.47  % (22209)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.49  % (22213)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.49  % (22194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (22198)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (22191)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.49  % (22193)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.49  % (22214)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.49  % (22196)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (22195)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (22205)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (22203)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (22192)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (22204)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (22206)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.51  % (22210)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (22197)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.52  % (22208)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.52  % (22208)Refutation not found, incomplete strategy% (22208)------------------------------
% 0.20/0.52  % (22208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22208)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (22208)Memory used [KB]: 1663
% 0.20/0.52  % (22208)Time elapsed: 0.118 s
% 0.20/0.52  % (22208)------------------------------
% 0.20/0.52  % (22208)------------------------------
% 0.20/0.52  % (22211)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.52  % (22194)Refutation not found, incomplete strategy% (22194)------------------------------
% 0.20/0.52  % (22194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22194)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (22194)Memory used [KB]: 10618
% 0.20/0.52  % (22194)Time elapsed: 0.084 s
% 0.20/0.52  % (22194)------------------------------
% 0.20/0.52  % (22194)------------------------------
% 0.20/0.52  % (22200)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.52  % (22202)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.53  % (22199)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.53  % (22207)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.53  % (22207)Refutation not found, incomplete strategy% (22207)------------------------------
% 0.20/0.53  % (22207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22212)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.54  % (22205)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 1.46/0.54  % (22207)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (22207)Memory used [KB]: 1663
% 1.46/0.54  % (22207)Time elapsed: 0.137 s
% 1.46/0.54  % (22207)------------------------------
% 1.46/0.54  % (22207)------------------------------
% 1.46/0.55  % SZS output start Proof for theBenchmark
% 1.46/0.55  fof(f874,plain,(
% 1.46/0.55    $false),
% 1.46/0.55    inference(avatar_sat_refutation,[],[f72,f73,f337,f873])).
% 1.46/0.55  fof(f873,plain,(
% 1.46/0.55    ~spl7_1 | spl7_2),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f872])).
% 1.46/0.55  fof(f872,plain,(
% 1.46/0.55    $false | (~spl7_1 | spl7_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f339,f870])).
% 1.46/0.55  fof(f870,plain,(
% 1.46/0.55    ~r2_hidden(sK4(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | (~spl7_1 | spl7_2)),
% 1.46/0.55    inference(superposition,[],[f852,f160])).
% 1.46/0.55  fof(f160,plain,(
% 1.46/0.55    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f42,f46])).
% 1.46/0.55  fof(f46,plain,(
% 1.46/0.55    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f15])).
% 1.46/0.55  fof(f15,plain,(
% 1.46/0.55    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.55    inference(ennf_transformation,[],[f7])).
% 1.46/0.55  fof(f7,axiom,(
% 1.46/0.55    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.46/0.55  fof(f42,plain,(
% 1.46/0.55    v1_relat_1(sK1)),
% 1.46/0.55    inference(cnf_transformation,[],[f27])).
% 1.46/0.55  fof(f27,plain,(
% 1.46/0.55    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 1.46/0.55  fof(f26,plain,(
% 1.46/0.55    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f25,plain,(
% 1.46/0.55    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.46/0.55    inference(flattening,[],[f24])).
% 1.46/0.55  fof(f24,plain,(
% 1.46/0.55    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.46/0.55    inference(nnf_transformation,[],[f14])).
% 1.46/0.55  fof(f14,plain,(
% 1.46/0.55    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.46/0.55    inference(ennf_transformation,[],[f11])).
% 1.46/0.55  fof(f11,negated_conjecture,(
% 1.46/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.46/0.55    inference(negated_conjecture,[],[f10])).
% 1.46/0.55  fof(f10,conjecture,(
% 1.46/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.46/0.55  fof(f852,plain,(
% 1.46/0.55    ( ! [X0] : (~r2_hidden(sK4(k2_relat_1(sK1),sK0),k9_relat_1(sK1,X0))) ) | (~spl7_1 | spl7_2)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f45,f340,f339,f846])).
% 1.46/0.55  fof(f846,plain,(
% 1.46/0.55    ( ! [X2,X3] : (~r1_xboole_0(X2,k1_xboole_0) | ~r2_hidden(X3,k9_relat_1(sK1,X2)) | ~r2_hidden(X3,k2_relat_1(sK1)) | ~r2_hidden(X3,sK0)) ) | ~spl7_1),
% 1.46/0.55    inference(superposition,[],[f762,f66])).
% 1.46/0.55  fof(f66,plain,(
% 1.46/0.55    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl7_1),
% 1.46/0.55    inference(avatar_component_clause,[],[f65])).
% 1.46/0.55  fof(f65,plain,(
% 1.46/0.55    spl7_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.46/0.55  fof(f762,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,k10_relat_1(sK1,X1)) | ~r2_hidden(X0,k9_relat_1(sK1,X2)) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,X1)) )),
% 1.46/0.55    inference(duplicate_literal_removal,[],[f756])).
% 1.46/0.55  fof(f756,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k9_relat_1(sK1,X2)) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,k9_relat_1(sK1,X2)) | ~r1_xboole_0(X2,k10_relat_1(sK1,X1))) )),
% 1.46/0.55    inference(resolution,[],[f526,f226])).
% 1.46/0.55  fof(f226,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,sK1),X2) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~r1_xboole_0(X1,X2)) )),
% 1.46/0.55    inference(resolution,[],[f210,f52])).
% 1.46/0.55  fof(f52,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f33])).
% 1.46/0.55  fof(f33,plain,(
% 1.46/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f32])).
% 1.46/0.55  fof(f32,plain,(
% 1.46/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f18,plain,(
% 1.46/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.46/0.55    inference(ennf_transformation,[],[f13])).
% 1.46/0.55  fof(f13,plain,(
% 1.46/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.46/0.55    inference(rectify,[],[f2])).
% 1.46/0.55  fof(f2,axiom,(
% 1.46/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.46/0.55  fof(f210,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,sK1),X1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 1.46/0.55    inference(resolution,[],[f58,f42])).
% 1.46/0.55  fof(f58,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f37])).
% 1.46/0.55  fof(f37,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.46/0.55  fof(f36,plain,(
% 1.46/0.55    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f35,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.46/0.55    inference(rectify,[],[f34])).
% 1.46/0.55  fof(f34,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.46/0.55    inference(nnf_transformation,[],[f22])).
% 1.46/0.55  fof(f22,plain,(
% 1.46/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.46/0.55    inference(ennf_transformation,[],[f6])).
% 1.46/0.55  fof(f6,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.46/0.55  fof(f526,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,sK1),k10_relat_1(sK1,X2)) | ~r2_hidden(X0,X2) | ~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 1.46/0.55    inference(global_subsumption,[],[f42,f521])).
% 1.46/0.55  fof(f521,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(sK1,X1)) | ~r2_hidden(X0,X2) | r2_hidden(sK5(X0,X1,sK1),k10_relat_1(sK1,X2)) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.46/0.55    inference(resolution,[],[f370,f63])).
% 1.46/0.55  fof(f63,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f41])).
% 1.46/0.55  fof(f41,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).
% 1.46/0.55  fof(f40,plain,(
% 1.46/0.55    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f39,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.46/0.55    inference(rectify,[],[f38])).
% 1.46/0.55  fof(f38,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.46/0.55    inference(nnf_transformation,[],[f23])).
% 1.46/0.55  fof(f23,plain,(
% 1.46/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.46/0.55    inference(ennf_transformation,[],[f8])).
% 1.46/0.55  fof(f8,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.46/0.55  fof(f370,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,sK1),X0),sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 1.46/0.55    inference(resolution,[],[f57,f42])).
% 1.46/0.55  fof(f57,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f37])).
% 1.46/0.55  fof(f340,plain,(
% 1.46/0.55    r2_hidden(sK4(k2_relat_1(sK1),sK0),sK0) | spl7_2),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f71,f51])).
% 1.46/0.55  fof(f51,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f33])).
% 1.46/0.55  fof(f71,plain,(
% 1.46/0.55    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl7_2),
% 1.46/0.55    inference(avatar_component_clause,[],[f69])).
% 1.46/0.55  fof(f69,plain,(
% 1.46/0.55    spl7_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.46/0.55  fof(f45,plain,(
% 1.46/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f5])).
% 1.46/0.55  fof(f5,axiom,(
% 1.46/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.46/0.55  fof(f339,plain,(
% 1.46/0.55    r2_hidden(sK4(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | spl7_2),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f71,f50])).
% 1.46/0.55  fof(f50,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f33])).
% 1.46/0.55  fof(f337,plain,(
% 1.46/0.55    spl7_1 | ~spl7_2),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f336])).
% 1.46/0.55  fof(f336,plain,(
% 1.46/0.55    $false | (spl7_1 | ~spl7_2)),
% 1.46/0.55    inference(subsumption_resolution,[],[f285,f334])).
% 1.46/0.55  fof(f334,plain,(
% 1.46/0.55    r2_hidden(sK6(sK2(k10_relat_1(sK1,sK0)),sK0,sK1),k2_relat_1(sK1)) | spl7_1),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f42,f82,f60])).
% 1.46/0.55  fof(f60,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f41])).
% 1.46/0.55  fof(f82,plain,(
% 1.46/0.55    r2_hidden(sK2(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) | spl7_1),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f67,f47])).
% 1.46/0.55  fof(f47,plain,(
% 1.46/0.55    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.46/0.55    inference(cnf_transformation,[],[f29])).
% 1.46/0.55  fof(f29,plain,(
% 1.46/0.55    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f28])).
% 1.46/0.55  fof(f28,plain,(
% 1.46/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f16,plain,(
% 1.46/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.46/0.55    inference(ennf_transformation,[],[f4])).
% 1.46/0.55  fof(f4,axiom,(
% 1.46/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.46/0.55  fof(f67,plain,(
% 1.46/0.55    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl7_1),
% 1.46/0.55    inference(avatar_component_clause,[],[f65])).
% 1.46/0.55  fof(f285,plain,(
% 1.46/0.55    ~r2_hidden(sK6(sK2(k10_relat_1(sK1,sK0)),sK0,sK1),k2_relat_1(sK1)) | (spl7_1 | ~spl7_2)),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f75,f258,f52])).
% 1.46/0.55  fof(f258,plain,(
% 1.46/0.55    r2_hidden(sK6(sK2(k10_relat_1(sK1,sK0)),sK0,sK1),sK0) | spl7_1),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f42,f82,f62])).
% 1.46/0.55  fof(f62,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f41])).
% 1.46/0.55  fof(f75,plain,(
% 1.46/0.55    r1_xboole_0(sK0,k2_relat_1(sK1)) | ~spl7_2),
% 1.46/0.55    inference(unit_resulting_resolution,[],[f70,f53])).
% 1.46/0.55  fof(f53,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f19])).
% 1.46/0.55  fof(f19,plain,(
% 1.46/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.46/0.55    inference(ennf_transformation,[],[f1])).
% 1.46/0.55  fof(f1,axiom,(
% 1.46/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.46/0.55  fof(f70,plain,(
% 1.46/0.55    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl7_2),
% 1.46/0.55    inference(avatar_component_clause,[],[f69])).
% 1.46/0.55  fof(f73,plain,(
% 1.46/0.55    spl7_1 | spl7_2),
% 1.46/0.55    inference(avatar_split_clause,[],[f43,f69,f65])).
% 1.46/0.55  fof(f43,plain,(
% 1.46/0.55    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.46/0.55    inference(cnf_transformation,[],[f27])).
% 1.46/0.55  fof(f72,plain,(
% 1.46/0.55    ~spl7_1 | ~spl7_2),
% 1.46/0.55    inference(avatar_split_clause,[],[f44,f69,f65])).
% 1.46/0.55  fof(f44,plain,(
% 1.46/0.55    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.46/0.55    inference(cnf_transformation,[],[f27])).
% 1.46/0.55  % SZS output end Proof for theBenchmark
% 1.46/0.55  % (22205)------------------------------
% 1.46/0.55  % (22205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (22205)Termination reason: Refutation
% 1.46/0.55  
% 1.46/0.55  % (22205)Memory used [KB]: 11129
% 1.46/0.55  % (22205)Time elapsed: 0.097 s
% 1.46/0.55  % (22205)------------------------------
% 1.46/0.55  % (22205)------------------------------
% 1.46/0.55  % (22190)Success in time 0.194 s
%------------------------------------------------------------------------------
