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
% DateTime   : Thu Dec  3 12:43:28 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 162 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  243 ( 549 expanded)
%              Number of equality atoms :   40 (  48 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f222,f226,f289,f296,f299])).

fof(f299,plain,
    ( spl7_10
    | ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl7_10
    | ~ spl7_13 ),
    inference(resolution,[],[f284,f230])).

fof(f230,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | spl7_10 ),
    inference(resolution,[],[f228,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f228,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl7_10 ),
    inference(resolution,[],[f221,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f221,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl7_10
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f284,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl7_13
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f296,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl7_14 ),
    inference(resolution,[],[f288,f34])).

fof(f34,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f21])).

fof(f21,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f288,plain,
    ( ~ r2_hidden(sK3,sK2)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl7_14
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f289,plain,
    ( spl7_13
    | ~ spl7_14
    | spl7_10 ),
    inference(avatar_split_clause,[],[f278,f219,f286,f282])).

fof(f278,plain,
    ( ~ r2_hidden(sK3,sK2)
    | r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | spl7_10 ),
    inference(superposition,[],[f124,f238])).

fof(f238,plain,
    ( sK3 = sK4(k3_xboole_0(sK0,sK1),sK1)
    | spl7_10 ),
    inference(resolution,[],[f230,f158])).

fof(f158,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_xboole_0(sK0,sK1),X0)
      | sK3 = sK4(k3_xboole_0(sK0,sK1),X0) ) ),
    inference(resolution,[],[f154,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f154,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_xboole_0(sK0,sK1))
      | sK3 = X1 ) ),
    inference(resolution,[],[f65,f137])).

fof(f137,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X0,k3_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f44,f58])).

fof(f58,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f33,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f65,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f57])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f124,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(X1,sK1),sK2)
      | r1_xboole_0(X1,sK1) ) ),
    inference(resolution,[],[f120,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f42,f35])).

fof(f35,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f226,plain,(
    spl7_9 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl7_9 ),
    inference(resolution,[],[f217,f127])).

fof(f127,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f123,f41])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK1,X0),sK2)
      | r1_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f120,f40])).

fof(f217,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl7_9
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f222,plain,
    ( ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f186,f219,f215])).

fof(f186,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f53,f66])).

fof(f66,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f43,f36])).

fof(f36,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:19:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (29676)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (29670)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (29669)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (29667)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (29688)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (29668)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (29690)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (29689)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (29677)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (29665)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (29678)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (29671)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (29680)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (29681)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.23/0.51  % (29677)Refutation found. Thanks to Tanya!
% 1.23/0.51  % SZS status Theorem for theBenchmark
% 1.23/0.51  % (29692)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.23/0.52  % (29672)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.23/0.52  % (29687)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.52  % (29682)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.23/0.52  % (29679)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.52  % (29683)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.23/0.52  % (29673)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.53  % (29675)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.53  % (29691)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.53  % (29693)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f300,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(avatar_sat_refutation,[],[f222,f226,f289,f296,f299])).
% 1.32/0.53  fof(f299,plain,(
% 1.32/0.53    spl7_10 | ~spl7_13),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f297])).
% 1.32/0.53  fof(f297,plain,(
% 1.32/0.53    $false | (spl7_10 | ~spl7_13)),
% 1.32/0.53    inference(resolution,[],[f284,f230])).
% 1.32/0.53  fof(f230,plain,(
% 1.32/0.53    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | spl7_10),
% 1.32/0.53    inference(resolution,[],[f228,f51])).
% 1.32/0.53  fof(f51,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f19])).
% 1.32/0.53  fof(f19,plain,(
% 1.32/0.53    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f6])).
% 1.32/0.53  fof(f6,axiom,(
% 1.32/0.53    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 1.32/0.53  fof(f228,plain,(
% 1.32/0.53    ~r1_xboole_0(sK0,sK1) | spl7_10),
% 1.32/0.53    inference(resolution,[],[f221,f43])).
% 1.32/0.53  fof(f43,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f17])).
% 1.32/0.53  fof(f17,plain,(
% 1.32/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f3])).
% 1.32/0.53  fof(f3,axiom,(
% 1.32/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.32/0.53  fof(f221,plain,(
% 1.32/0.53    ~r1_xboole_0(sK1,sK0) | spl7_10),
% 1.32/0.53    inference(avatar_component_clause,[],[f219])).
% 1.32/0.53  fof(f219,plain,(
% 1.32/0.53    spl7_10 <=> r1_xboole_0(sK1,sK0)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.32/0.53  fof(f284,plain,(
% 1.32/0.53    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | ~spl7_13),
% 1.32/0.53    inference(avatar_component_clause,[],[f282])).
% 1.32/0.53  fof(f282,plain,(
% 1.32/0.53    spl7_13 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.32/0.53  fof(f296,plain,(
% 1.32/0.53    spl7_14),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f295])).
% 1.32/0.53  fof(f295,plain,(
% 1.32/0.53    $false | spl7_14),
% 1.32/0.53    inference(resolution,[],[f288,f34])).
% 1.32/0.53  fof(f34,plain,(
% 1.32/0.53    r2_hidden(sK3,sK2)),
% 1.32/0.53    inference(cnf_transformation,[],[f22])).
% 1.32/0.53  fof(f22,plain,(
% 1.32/0.53    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f21])).
% 1.32/0.53  fof(f21,plain,(
% 1.32/0.53    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f15,plain,(
% 1.32/0.53    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.32/0.53    inference(flattening,[],[f14])).
% 1.32/0.53  fof(f14,plain,(
% 1.32/0.53    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.32/0.53    inference(ennf_transformation,[],[f12])).
% 1.32/0.53  fof(f12,negated_conjecture,(
% 1.32/0.53    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.32/0.53    inference(negated_conjecture,[],[f11])).
% 1.32/0.53  fof(f11,conjecture,(
% 1.32/0.53    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.32/0.53  fof(f288,plain,(
% 1.32/0.53    ~r2_hidden(sK3,sK2) | spl7_14),
% 1.32/0.53    inference(avatar_component_clause,[],[f286])).
% 1.32/0.53  fof(f286,plain,(
% 1.32/0.53    spl7_14 <=> r2_hidden(sK3,sK2)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.32/0.53  fof(f289,plain,(
% 1.32/0.53    spl7_13 | ~spl7_14 | spl7_10),
% 1.32/0.53    inference(avatar_split_clause,[],[f278,f219,f286,f282])).
% 1.32/0.53  fof(f278,plain,(
% 1.32/0.53    ~r2_hidden(sK3,sK2) | r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | spl7_10),
% 1.32/0.53    inference(superposition,[],[f124,f238])).
% 1.32/0.53  fof(f238,plain,(
% 1.32/0.53    sK3 = sK4(k3_xboole_0(sK0,sK1),sK1) | spl7_10),
% 1.32/0.53    inference(resolution,[],[f230,f158])).
% 1.32/0.53  fof(f158,plain,(
% 1.32/0.53    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X0) | sK3 = sK4(k3_xboole_0(sK0,sK1),X0)) )),
% 1.32/0.53    inference(resolution,[],[f154,f40])).
% 1.32/0.53  fof(f40,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f24])).
% 1.32/0.53  fof(f24,plain,(
% 1.32/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f23])).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f16,plain,(
% 1.32/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(ennf_transformation,[],[f13])).
% 1.32/0.53  fof(f13,plain,(
% 1.32/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(rectify,[],[f4])).
% 1.32/0.53  fof(f4,axiom,(
% 1.32/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.32/0.53  fof(f154,plain,(
% 1.32/0.53    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK0,sK1)) | sK3 = X1) )),
% 1.32/0.53    inference(resolution,[],[f65,f137])).
% 1.32/0.53  fof(f137,plain,(
% 1.32/0.53    ( ! [X0] : (r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) | ~r2_hidden(X0,k3_xboole_0(sK0,sK1))) )),
% 1.32/0.53    inference(resolution,[],[f44,f58])).
% 1.32/0.53  fof(f58,plain,(
% 1.32/0.53    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.32/0.53    inference(definition_unfolding,[],[f33,f57])).
% 1.32/0.53  fof(f57,plain,(
% 1.32/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f37,f56])).
% 1.32/0.53  fof(f56,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f39,f52])).
% 1.32/0.53  fof(f52,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f10])).
% 1.32/0.53  fof(f10,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.53  fof(f39,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f9])).
% 1.32/0.53  fof(f9,axiom,(
% 1.32/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.53  fof(f37,plain,(
% 1.32/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f8])).
% 1.32/0.53  fof(f8,axiom,(
% 1.32/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.53  fof(f33,plain,(
% 1.32/0.53    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.32/0.53    inference(cnf_transformation,[],[f22])).
% 1.32/0.53  fof(f44,plain,(
% 1.32/0.53    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f28])).
% 1.32/0.53  fof(f28,plain,(
% 1.32/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.53    inference(rectify,[],[f25])).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.53    inference(nnf_transformation,[],[f18])).
% 1.32/0.53  fof(f18,plain,(
% 1.32/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f2])).
% 1.32/0.53  fof(f2,axiom,(
% 1.32/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.32/0.53  fof(f65,plain,(
% 1.32/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.32/0.53    inference(equality_resolution,[],[f62])).
% 1.32/0.53  fof(f62,plain,(
% 1.32/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.32/0.53    inference(definition_unfolding,[],[f47,f57])).
% 1.32/0.53  fof(f47,plain,(
% 1.32/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.32/0.53    inference(cnf_transformation,[],[f32])).
% 1.32/0.53  fof(f32,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f30,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.53    inference(rectify,[],[f29])).
% 1.32/0.53  fof(f29,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.53    inference(nnf_transformation,[],[f7])).
% 1.32/0.53  fof(f7,axiom,(
% 1.32/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.32/0.53  fof(f124,plain,(
% 1.32/0.53    ( ! [X1] : (~r2_hidden(sK4(X1,sK1),sK2) | r1_xboole_0(X1,sK1)) )),
% 1.32/0.53    inference(resolution,[],[f120,f41])).
% 1.32/0.53  fof(f41,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f24])).
% 1.32/0.53  fof(f120,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2)) )),
% 1.32/0.53    inference(resolution,[],[f42,f35])).
% 1.32/0.53  fof(f35,plain,(
% 1.32/0.53    r1_xboole_0(sK2,sK1)),
% 1.32/0.53    inference(cnf_transformation,[],[f22])).
% 1.32/0.53  fof(f42,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f24])).
% 1.32/0.53  fof(f226,plain,(
% 1.32/0.53    spl7_9),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f223])).
% 1.32/0.53  fof(f223,plain,(
% 1.32/0.53    $false | spl7_9),
% 1.32/0.53    inference(resolution,[],[f217,f127])).
% 1.32/0.53  fof(f127,plain,(
% 1.32/0.53    r1_xboole_0(sK1,sK2)),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f126])).
% 1.32/0.53  fof(f126,plain,(
% 1.32/0.53    r1_xboole_0(sK1,sK2) | r1_xboole_0(sK1,sK2)),
% 1.32/0.53    inference(resolution,[],[f123,f41])).
% 1.32/0.53  fof(f123,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(sK4(sK1,X0),sK2) | r1_xboole_0(sK1,X0)) )),
% 1.32/0.53    inference(resolution,[],[f120,f40])).
% 1.32/0.53  fof(f217,plain,(
% 1.32/0.53    ~r1_xboole_0(sK1,sK2) | spl7_9),
% 1.32/0.53    inference(avatar_component_clause,[],[f215])).
% 1.32/0.53  fof(f215,plain,(
% 1.32/0.53    spl7_9 <=> r1_xboole_0(sK1,sK2)),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.32/0.53  fof(f222,plain,(
% 1.32/0.53    ~spl7_9 | ~spl7_10),
% 1.32/0.53    inference(avatar_split_clause,[],[f186,f219,f215])).
% 1.32/0.53  fof(f186,plain,(
% 1.32/0.53    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 1.32/0.53    inference(resolution,[],[f53,f66])).
% 1.32/0.53  fof(f66,plain,(
% 1.32/0.53    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.32/0.53    inference(resolution,[],[f43,f36])).
% 1.32/0.53  fof(f36,plain,(
% 1.32/0.53    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.32/0.53    inference(cnf_transformation,[],[f22])).
% 1.32/0.53  fof(f53,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f20])).
% 1.32/0.53  fof(f20,plain,(
% 1.32/0.53    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.32/0.53    inference(ennf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (29677)------------------------------
% 1.32/0.53  % (29677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (29677)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (29677)Memory used [KB]: 6396
% 1.32/0.53  % (29677)Time elapsed: 0.106 s
% 1.32/0.53  % (29677)------------------------------
% 1.32/0.53  % (29677)------------------------------
% 1.32/0.53  % (29662)Success in time 0.177 s
%------------------------------------------------------------------------------
