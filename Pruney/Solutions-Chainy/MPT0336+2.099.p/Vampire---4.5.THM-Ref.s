%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 137 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  363 ( 499 expanded)
%              Number of equality atoms :   89 (  92 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f104,f128,f162,f173,f245,f248,f383])).

fof(f383,plain,
    ( spl7_6
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f369,f127])).

fof(f127,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_6
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f369,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f256,f105])).

fof(f105,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f72,f66])).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f72,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f256,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_tarski(sK3))
        | r2_hidden(X2,sK1) )
    | ~ spl7_7 ),
    inference(superposition,[],[f75,f141])).

fof(f141,plain,
    ( k3_xboole_0(sK0,sK1) = k1_tarski(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_7
  <=> k3_xboole_0(sK0,sK1) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f248,plain,
    ( spl7_7
    | spl7_8
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f246,f95,f143,f139])).

fof(f143,plain,
    ( spl7_8
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f95,plain,
    ( spl7_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f246,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | k3_xboole_0(sK0,sK1) = k1_tarski(sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f97,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f97,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f245,plain,
    ( ~ spl7_10
    | spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f242,f101,f80,f170])).

fof(f170,plain,
    ( spl7_10
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f80,plain,
    ( spl7_1
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f101,plain,
    ( spl7_5
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f242,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f232,f103])).

fof(f103,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f232,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0)
    | spl7_1 ),
    inference(resolution,[],[f132,f82])).

fof(f82,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f132,plain,(
    ! [X12,X10,X11] :
      ( r1_xboole_0(k2_xboole_0(X11,X12),X10)
      | ~ r1_xboole_0(X10,X12)
      | ~ r1_xboole_0(X10,X11) ) ),
    inference(resolution,[],[f41,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f173,plain,
    ( spl7_10
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f168,f159,f170])).

fof(f159,plain,
    ( spl7_9
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f168,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl7_9 ),
    inference(resolution,[],[f161,f47])).

fof(f161,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f159])).

fof(f162,plain,
    ( spl7_9
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f157,f143,f159])).

fof(f157,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl7_8 ),
    inference(trivial_inequality_removal,[],[f156])).

fof(f156,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1)
    | ~ spl7_8 ),
    inference(superposition,[],[f46,f145])).

fof(f145,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f128,plain,
    ( ~ spl7_6
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f121,f90,f85,f125])).

fof(f85,plain,
    ( spl7_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f90,plain,
    ( spl7_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f121,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f119,f92])).

fof(f92,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f50,f87])).

fof(f87,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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

fof(f104,plain,
    ( spl7_5
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f99,f85,f101])).

fof(f99,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f47,f87])).

fof(f98,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f21])).

% (8457)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f21,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20])).

fof(f20,plain,
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

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f93,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f38,f90])).

fof(f38,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f39,f85])).

fof(f39,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (8456)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (8474)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (8465)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (8474)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (8455)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.45/0.55  % SZS output start Proof for theBenchmark
% 1.45/0.56  fof(f384,plain,(
% 1.45/0.56    $false),
% 1.45/0.56    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f104,f128,f162,f173,f245,f248,f383])).
% 1.45/0.56  fof(f383,plain,(
% 1.45/0.56    spl7_6 | ~spl7_7),
% 1.45/0.56    inference(avatar_contradiction_clause,[],[f382])).
% 1.45/0.56  fof(f382,plain,(
% 1.45/0.56    $false | (spl7_6 | ~spl7_7)),
% 1.45/0.56    inference(subsumption_resolution,[],[f369,f127])).
% 1.45/0.56  fof(f127,plain,(
% 1.45/0.56    ~r2_hidden(sK3,sK1) | spl7_6),
% 1.45/0.56    inference(avatar_component_clause,[],[f125])).
% 1.45/0.56  fof(f125,plain,(
% 1.45/0.56    spl7_6 <=> r2_hidden(sK3,sK1)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.45/0.56  fof(f369,plain,(
% 1.45/0.56    r2_hidden(sK3,sK1) | ~spl7_7),
% 1.45/0.56    inference(resolution,[],[f256,f105])).
% 1.45/0.56  fof(f105,plain,(
% 1.45/0.56    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.45/0.56    inference(superposition,[],[f72,f66])).
% 1.45/0.56  fof(f66,plain,(
% 1.45/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f7])).
% 1.45/0.56  fof(f7,axiom,(
% 1.45/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.56  fof(f72,plain,(
% 1.45/0.56    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.45/0.56    inference(equality_resolution,[],[f71])).
% 1.45/0.56  fof(f71,plain,(
% 1.45/0.56    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.45/0.56    inference(equality_resolution,[],[f52])).
% 1.45/0.56  fof(f52,plain,(
% 1.45/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.45/0.56    inference(cnf_transformation,[],[f29])).
% 1.45/0.56  fof(f29,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 1.45/0.56  fof(f28,plain,(
% 1.45/0.56    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f27,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.56    inference(rectify,[],[f26])).
% 1.45/0.56  fof(f26,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.56    inference(flattening,[],[f25])).
% 1.45/0.56  fof(f25,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.56    inference(nnf_transformation,[],[f6])).
% 1.45/0.56  fof(f6,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.45/0.56  fof(f256,plain,(
% 1.45/0.56    ( ! [X2] : (~r2_hidden(X2,k1_tarski(sK3)) | r2_hidden(X2,sK1)) ) | ~spl7_7),
% 1.45/0.56    inference(superposition,[],[f75,f141])).
% 1.45/0.56  fof(f141,plain,(
% 1.45/0.56    k3_xboole_0(sK0,sK1) = k1_tarski(sK3) | ~spl7_7),
% 1.45/0.56    inference(avatar_component_clause,[],[f139])).
% 1.45/0.56  fof(f139,plain,(
% 1.45/0.56    spl7_7 <=> k3_xboole_0(sK0,sK1) = k1_tarski(sK3)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.45/0.56  fof(f75,plain,(
% 1.45/0.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 1.45/0.56    inference(equality_resolution,[],[f58])).
% 1.45/0.56  fof(f58,plain,(
% 1.45/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.45/0.56    inference(cnf_transformation,[],[f34])).
% 1.45/0.56  fof(f34,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).
% 1.45/0.56  fof(f33,plain,(
% 1.45/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f32,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.56    inference(rectify,[],[f31])).
% 1.45/0.56  fof(f31,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.56    inference(flattening,[],[f30])).
% 1.45/0.56  fof(f30,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.56    inference(nnf_transformation,[],[f1])).
% 1.45/0.56  fof(f1,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.45/0.56  fof(f248,plain,(
% 1.45/0.56    spl7_7 | spl7_8 | ~spl7_4),
% 1.45/0.56    inference(avatar_split_clause,[],[f246,f95,f143,f139])).
% 1.45/0.56  fof(f143,plain,(
% 1.45/0.56    spl7_8 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.45/0.56  fof(f95,plain,(
% 1.45/0.56    spl7_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.45/0.56  fof(f246,plain,(
% 1.45/0.56    k1_xboole_0 = k3_xboole_0(sK0,sK1) | k3_xboole_0(sK0,sK1) = k1_tarski(sK3) | ~spl7_4),
% 1.45/0.56    inference(resolution,[],[f97,f63])).
% 1.45/0.56  fof(f63,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.45/0.56    inference(cnf_transformation,[],[f36])).
% 1.45/0.56  fof(f36,plain,(
% 1.45/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.45/0.56    inference(flattening,[],[f35])).
% 1.45/0.56  fof(f35,plain,(
% 1.45/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.45/0.56    inference(nnf_transformation,[],[f10])).
% 1.45/0.56  fof(f10,axiom,(
% 1.45/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.45/0.56  fof(f97,plain,(
% 1.45/0.56    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl7_4),
% 1.45/0.56    inference(avatar_component_clause,[],[f95])).
% 1.45/0.56  fof(f245,plain,(
% 1.45/0.56    ~spl7_10 | spl7_1 | ~spl7_5),
% 1.45/0.56    inference(avatar_split_clause,[],[f242,f101,f80,f170])).
% 1.45/0.56  fof(f170,plain,(
% 1.45/0.56    spl7_10 <=> r1_xboole_0(sK1,sK0)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.45/0.56  fof(f80,plain,(
% 1.45/0.56    spl7_1 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.45/0.56  fof(f101,plain,(
% 1.45/0.56    spl7_5 <=> r1_xboole_0(sK1,sK2)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.45/0.56  fof(f242,plain,(
% 1.45/0.56    ~r1_xboole_0(sK1,sK0) | (spl7_1 | ~spl7_5)),
% 1.45/0.56    inference(subsumption_resolution,[],[f232,f103])).
% 1.45/0.56  fof(f103,plain,(
% 1.45/0.56    r1_xboole_0(sK1,sK2) | ~spl7_5),
% 1.45/0.56    inference(avatar_component_clause,[],[f101])).
% 1.45/0.56  fof(f232,plain,(
% 1.45/0.56    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0) | spl7_1),
% 1.45/0.56    inference(resolution,[],[f132,f82])).
% 1.45/0.56  fof(f82,plain,(
% 1.45/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl7_1),
% 1.45/0.56    inference(avatar_component_clause,[],[f80])).
% 1.45/0.56  fof(f132,plain,(
% 1.45/0.56    ( ! [X12,X10,X11] : (r1_xboole_0(k2_xboole_0(X11,X12),X10) | ~r1_xboole_0(X10,X12) | ~r1_xboole_0(X10,X11)) )),
% 1.45/0.56    inference(resolution,[],[f41,f47])).
% 1.45/0.56  fof(f47,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f18])).
% 1.45/0.56  fof(f18,plain,(
% 1.45/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.45/0.56    inference(ennf_transformation,[],[f3])).
% 1.45/0.56  fof(f3,axiom,(
% 1.45/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.45/0.56  fof(f41,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f17])).
% 1.45/0.56  fof(f17,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.45/0.56    inference(ennf_transformation,[],[f5])).
% 1.45/0.56  fof(f5,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.45/0.56  fof(f173,plain,(
% 1.45/0.56    spl7_10 | ~spl7_9),
% 1.45/0.56    inference(avatar_split_clause,[],[f168,f159,f170])).
% 1.45/0.56  fof(f159,plain,(
% 1.45/0.56    spl7_9 <=> r1_xboole_0(sK0,sK1)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.45/0.56  fof(f168,plain,(
% 1.45/0.56    r1_xboole_0(sK1,sK0) | ~spl7_9),
% 1.45/0.56    inference(resolution,[],[f161,f47])).
% 1.45/0.56  fof(f161,plain,(
% 1.45/0.56    r1_xboole_0(sK0,sK1) | ~spl7_9),
% 1.45/0.56    inference(avatar_component_clause,[],[f159])).
% 1.45/0.56  fof(f162,plain,(
% 1.45/0.56    spl7_9 | ~spl7_8),
% 1.45/0.56    inference(avatar_split_clause,[],[f157,f143,f159])).
% 1.45/0.56  fof(f157,plain,(
% 1.45/0.56    r1_xboole_0(sK0,sK1) | ~spl7_8),
% 1.45/0.56    inference(trivial_inequality_removal,[],[f156])).
% 1.45/0.56  fof(f156,plain,(
% 1.45/0.56    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1) | ~spl7_8),
% 1.45/0.56    inference(superposition,[],[f46,f145])).
% 1.45/0.56  fof(f145,plain,(
% 1.45/0.56    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl7_8),
% 1.45/0.56    inference(avatar_component_clause,[],[f143])).
% 1.45/0.56  fof(f46,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f22])).
% 1.45/0.56  fof(f22,plain,(
% 1.45/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.45/0.56    inference(nnf_transformation,[],[f2])).
% 1.45/0.56  fof(f2,axiom,(
% 1.45/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.45/0.56  fof(f128,plain,(
% 1.45/0.56    ~spl7_6 | ~spl7_2 | ~spl7_3),
% 1.45/0.56    inference(avatar_split_clause,[],[f121,f90,f85,f125])).
% 1.45/0.56  fof(f85,plain,(
% 1.45/0.56    spl7_2 <=> r1_xboole_0(sK2,sK1)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.45/0.56  fof(f90,plain,(
% 1.45/0.56    spl7_3 <=> r2_hidden(sK3,sK2)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.45/0.56  fof(f121,plain,(
% 1.45/0.56    ~r2_hidden(sK3,sK1) | (~spl7_2 | ~spl7_3)),
% 1.45/0.56    inference(resolution,[],[f119,f92])).
% 1.45/0.56  fof(f92,plain,(
% 1.45/0.56    r2_hidden(sK3,sK2) | ~spl7_3),
% 1.45/0.56    inference(avatar_component_clause,[],[f90])).
% 1.45/0.56  fof(f119,plain,(
% 1.45/0.56    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) ) | ~spl7_2),
% 1.45/0.56    inference(resolution,[],[f50,f87])).
% 1.45/0.56  fof(f87,plain,(
% 1.45/0.56    r1_xboole_0(sK2,sK1) | ~spl7_2),
% 1.45/0.56    inference(avatar_component_clause,[],[f85])).
% 1.45/0.56  fof(f50,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f24])).
% 1.45/0.56  fof(f24,plain,(
% 1.45/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f23])).
% 1.45/0.56  fof(f23,plain,(
% 1.45/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f19,plain,(
% 1.45/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.56    inference(ennf_transformation,[],[f14])).
% 1.45/0.56  fof(f14,plain,(
% 1.45/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.56    inference(rectify,[],[f4])).
% 1.45/0.56  fof(f4,axiom,(
% 1.45/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.45/0.56  fof(f104,plain,(
% 1.45/0.56    spl7_5 | ~spl7_2),
% 1.45/0.56    inference(avatar_split_clause,[],[f99,f85,f101])).
% 1.45/0.56  fof(f99,plain,(
% 1.45/0.56    r1_xboole_0(sK1,sK2) | ~spl7_2),
% 1.45/0.56    inference(resolution,[],[f47,f87])).
% 1.45/0.56  fof(f98,plain,(
% 1.45/0.56    spl7_4),
% 1.45/0.56    inference(avatar_split_clause,[],[f37,f95])).
% 1.45/0.56  fof(f37,plain,(
% 1.45/0.56    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.45/0.56    inference(cnf_transformation,[],[f21])).
% 1.45/0.56  % (8457)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.56  fof(f21,plain,(
% 1.45/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.45/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20])).
% 1.45/0.56  fof(f20,plain,(
% 1.45/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f16,plain,(
% 1.45/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.45/0.56    inference(flattening,[],[f15])).
% 1.45/0.56  fof(f15,plain,(
% 1.45/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.45/0.56    inference(ennf_transformation,[],[f13])).
% 1.45/0.56  fof(f13,negated_conjecture,(
% 1.45/0.56    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.45/0.56    inference(negated_conjecture,[],[f12])).
% 1.45/0.56  fof(f12,conjecture,(
% 1.45/0.56    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.45/0.56  fof(f93,plain,(
% 1.45/0.56    spl7_3),
% 1.45/0.56    inference(avatar_split_clause,[],[f38,f90])).
% 1.45/0.56  fof(f38,plain,(
% 1.45/0.56    r2_hidden(sK3,sK2)),
% 1.45/0.56    inference(cnf_transformation,[],[f21])).
% 1.45/0.56  fof(f88,plain,(
% 1.45/0.56    spl7_2),
% 1.45/0.56    inference(avatar_split_clause,[],[f39,f85])).
% 1.45/0.56  fof(f39,plain,(
% 1.45/0.56    r1_xboole_0(sK2,sK1)),
% 1.45/0.56    inference(cnf_transformation,[],[f21])).
% 1.45/0.56  fof(f83,plain,(
% 1.45/0.56    ~spl7_1),
% 1.45/0.56    inference(avatar_split_clause,[],[f40,f80])).
% 1.45/0.56  fof(f40,plain,(
% 1.45/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.45/0.56    inference(cnf_transformation,[],[f21])).
% 1.45/0.56  % SZS output end Proof for theBenchmark
% 1.45/0.56  % (8474)------------------------------
% 1.45/0.56  % (8474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (8474)Termination reason: Refutation
% 1.45/0.56  
% 1.45/0.56  % (8474)Memory used [KB]: 6396
% 1.45/0.56  % (8474)Time elapsed: 0.134 s
% 1.45/0.56  % (8474)------------------------------
% 1.45/0.56  % (8474)------------------------------
% 1.45/0.56  % (8448)Success in time 0.203 s
%------------------------------------------------------------------------------
