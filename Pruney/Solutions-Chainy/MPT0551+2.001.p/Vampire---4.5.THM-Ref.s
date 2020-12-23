%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 284 expanded)
%              Number of leaves         :   21 ( 105 expanded)
%              Depth                    :   11
%              Number of atoms          :  398 (1361 expanded)
%              Number of equality atoms :   32 ( 171 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1093,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f107,f194,f243,f246,f247,f448,f959,f960,f1085,f1088,f1091,f1092])).

fof(f1092,plain,
    ( ~ spl9_12
    | ~ spl9_15
    | spl9_16 ),
    inference(avatar_split_clause,[],[f1069,f256,f240,f187])).

fof(f187,plain,
    ( spl9_12
  <=> r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f240,plain,
    ( spl9_15
  <=> ! [X0] :
        ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),X0)
        | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f256,plain,
    ( spl9_16
  <=> r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f1069,plain,
    ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK0)
    | ~ spl9_15
    | spl9_16 ),
    inference(resolution,[],[f241,f257])).

fof(f257,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | spl9_16 ),
    inference(avatar_component_clause,[],[f256])).

fof(f241,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,X0))
        | ~ r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),X0) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f240])).

fof(f1091,plain,
    ( ~ spl9_17
    | spl9_2 ),
    inference(avatar_split_clause,[],[f272,f89,f260])).

fof(f260,plain,
    ( spl9_17
  <=> r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f89,plain,
    ( spl9_2
  <=> r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f272,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | spl9_2 ),
    inference(resolution,[],[f90,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & ~ r2_hidden(sK7(X0,X1,X2),X0) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( r2_hidden(sK7(X0,X1,X2),X1)
            | r2_hidden(sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & ~ r2_hidden(sK7(X0,X1,X2),X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( r2_hidden(sK7(X0,X1,X2),X1)
          | r2_hidden(sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f90,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f1088,plain,
    ( ~ spl9_16
    | spl9_2 ),
    inference(avatar_split_clause,[],[f271,f89,f256])).

fof(f271,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | spl9_2 ),
    inference(resolution,[],[f90,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1085,plain,
    ( ~ spl9_13
    | ~ spl9_15
    | spl9_17 ),
    inference(avatar_split_clause,[],[f1070,f260,f240,f191])).

fof(f191,plain,
    ( spl9_13
  <=> r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f1070,plain,
    ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK1)
    | ~ spl9_15
    | spl9_17 ),
    inference(resolution,[],[f241,f261])).

fof(f261,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | spl9_17 ),
    inference(avatar_component_clause,[],[f260])).

fof(f960,plain,
    ( ~ spl9_17
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f957,f103,f260])).

fof(f103,plain,
    ( spl9_5
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK0,sK1))
        | ~ r2_hidden(k4_tarski(X0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f957,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f944])).

fof(f944,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | ~ spl9_5 ),
    inference(resolution,[],[f282,f70])).

fof(f70,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK6(X3,X4,sK2),k2_xboole_0(X5,X4))
      | ~ r2_hidden(X3,k9_relat_1(sK2,X4)) ) ),
    inference(resolution,[],[f61,f47])).

fof(f61,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK6(X4,X5,sK2),X5)
      | ~ r2_hidden(X4,k9_relat_1(sK2,X5)) ) ),
    inference(resolution,[],[f26,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
            & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(f282,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),X0,sK2),k2_xboole_0(sK0,sK1))
        | ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,X0)) )
    | ~ spl9_5 ),
    inference(resolution,[],[f104,f60])).

fof(f60,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK6(X2,X3,sK2),X2),sK2)
      | ~ r2_hidden(X2,k9_relat_1(sK2,X3)) ) ),
    inference(resolution,[],[f26,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2)
        | ~ r2_hidden(X0,k2_xboole_0(sK0,sK1)) )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f959,plain,
    ( ~ spl9_16
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f958,f103,f256])).

fof(f958,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f943])).

fof(f943,plain,
    ( ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ spl9_5 ),
    inference(resolution,[],[f282,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,sK2),k2_xboole_0(X1,X2))
      | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f61,f48])).

fof(f448,plain,
    ( spl9_16
    | spl9_17
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f248,f89,f260,f256])).

fof(f248,plain,
    ( r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ spl9_2 ),
    inference(resolution,[],[f91,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,
    ( r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f247,plain,
    ( spl9_2
    | spl9_3 ),
    inference(avatar_split_clause,[],[f217,f93,f89])).

fof(f93,plain,
    ( spl9_3
  <=> r2_hidden(k4_tarski(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f217,plain,
    ( r2_hidden(k4_tarski(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2)
    | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
    ~ sQ8_eqProxy(k9_relat_1(sK2,k2_xboole_0(sK0,sK1)),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(equality_proxy_replacement,[],[f27,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f27,plain,(
    k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X21,X22] :
      ( sQ8_eqProxy(k9_relat_1(sK2,X21),X22)
      | r2_hidden(k4_tarski(sK4(sK2,X21,X22),sK3(sK2,X21,X22)),sK2)
      | r2_hidden(sK3(sK2,X21,X22),X22) ) ),
    inference(resolution,[],[f26,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sQ8_eqProxy(k9_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f31,f50])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f12,f15,f14,f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f246,plain,
    ( ~ spl9_2
    | spl9_5 ),
    inference(avatar_split_clause,[],[f216,f103,f89])).

fof(f216,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(k4_tarski(X0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2)
      | ~ r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ) ),
    inference(resolution,[],[f66,f51])).

fof(f66,plain,(
    ! [X17,X18,X16] :
      ( sQ8_eqProxy(k9_relat_1(sK2,X16),X17)
      | ~ r2_hidden(X18,X16)
      | ~ r2_hidden(k4_tarski(X18,sK3(sK2,X16,X17)),sK2)
      | ~ r2_hidden(sK3(sK2,X16,X17),X17) ) ),
    inference(resolution,[],[f26,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( sQ8_eqProxy(k9_relat_1(X0,X1),X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f33,f50])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f243,plain,
    ( spl9_15
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f226,f93,f240])).

fof(f226,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),X1)
        | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,X1)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f95,f63])).

fof(f63,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X11,X9),sK2)
      | ~ r2_hidden(X11,X10)
      | r2_hidden(X9,k9_relat_1(sK2,X10)) ) ),
    inference(resolution,[],[f26,f44])).

fof(f44,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,
    ( r2_hidden(k4_tarski(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f194,plain,
    ( spl9_12
    | spl9_13
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f180,f98,f191,f187])).

fof(f98,plain,
    ( spl9_4
  <=> r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f180,plain,
    ( r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK1)
    | r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f100,f49])).

fof(f100,plain,
    ( r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(sK0,sK1))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f107,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl9_1 ),
    inference(resolution,[],[f87,f26])).

fof(f87,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl9_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f101,plain,
    ( ~ spl9_1
    | spl9_2
    | spl9_4 ),
    inference(avatar_split_clause,[],[f82,f98,f89,f85])).

fof(f82,plain,
    ( r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sQ8_eqProxy(k9_relat_1(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f32,f50])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:43:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (19840)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (19839)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (19832)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (19837)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (19836)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (19848)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (19846)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (19852)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (19852)Refutation not found, incomplete strategy% (19852)------------------------------
% 0.21/0.51  % (19852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19852)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19852)Memory used [KB]: 10618
% 0.21/0.51  % (19852)Time elapsed: 0.095 s
% 0.21/0.51  % (19852)------------------------------
% 0.21/0.51  % (19852)------------------------------
% 0.21/0.52  % (19845)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (19835)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (19834)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (19846)Refutation not found, incomplete strategy% (19846)------------------------------
% 0.21/0.52  % (19846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19846)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19846)Memory used [KB]: 10618
% 0.21/0.52  % (19846)Time elapsed: 0.042 s
% 0.21/0.52  % (19846)------------------------------
% 0.21/0.52  % (19846)------------------------------
% 0.21/0.52  % (19841)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (19844)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (19842)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (19838)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.53  % (19843)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (19843)Refutation not found, incomplete strategy% (19843)------------------------------
% 0.21/0.53  % (19843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19843)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19843)Memory used [KB]: 10618
% 0.21/0.53  % (19843)Time elapsed: 0.104 s
% 0.21/0.53  % (19843)------------------------------
% 0.21/0.53  % (19843)------------------------------
% 0.21/0.53  % (19833)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (19833)Refutation not found, incomplete strategy% (19833)------------------------------
% 0.21/0.53  % (19833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19833)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19833)Memory used [KB]: 10490
% 0.21/0.53  % (19833)Time elapsed: 0.109 s
% 0.21/0.53  % (19833)------------------------------
% 0.21/0.53  % (19833)------------------------------
% 0.21/0.53  % (19851)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (19847)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (19850)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.54  % (19849)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.57  % (19844)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 1.70/0.58  % SZS output start Proof for theBenchmark
% 1.70/0.58  fof(f1093,plain,(
% 1.70/0.58    $false),
% 1.70/0.58    inference(avatar_sat_refutation,[],[f101,f107,f194,f243,f246,f247,f448,f959,f960,f1085,f1088,f1091,f1092])).
% 1.70/0.58  fof(f1092,plain,(
% 1.70/0.58    ~spl9_12 | ~spl9_15 | spl9_16),
% 1.70/0.58    inference(avatar_split_clause,[],[f1069,f256,f240,f187])).
% 1.70/0.58  fof(f187,plain,(
% 1.70/0.58    spl9_12 <=> r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK0)),
% 1.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.70/0.58  fof(f240,plain,(
% 1.70/0.58    spl9_15 <=> ! [X0] : (~r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),X0) | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,X0)))),
% 1.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.70/0.58  fof(f256,plain,(
% 1.70/0.58    spl9_16 <=> r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))),
% 1.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.70/0.58  fof(f1069,plain,(
% 1.70/0.58    ~r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK0) | (~spl9_15 | spl9_16)),
% 1.70/0.58    inference(resolution,[],[f241,f257])).
% 1.70/0.58  fof(f257,plain,(
% 1.70/0.58    ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | spl9_16),
% 1.70/0.58    inference(avatar_component_clause,[],[f256])).
% 1.70/0.58  fof(f241,plain,(
% 1.70/0.58    ( ! [X0] : (r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,X0)) | ~r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),X0)) ) | ~spl9_15),
% 1.70/0.58    inference(avatar_component_clause,[],[f240])).
% 1.70/0.58  fof(f1091,plain,(
% 1.70/0.58    ~spl9_17 | spl9_2),
% 1.70/0.58    inference(avatar_split_clause,[],[f272,f89,f260])).
% 1.70/0.58  fof(f260,plain,(
% 1.70/0.58    spl9_17 <=> r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))),
% 1.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 1.70/0.58  fof(f89,plain,(
% 1.70/0.58    spl9_2 <=> r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 1.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.70/0.58  fof(f272,plain,(
% 1.70/0.58    ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) | spl9_2),
% 1.70/0.58    inference(resolution,[],[f90,f47])).
% 1.70/0.58  fof(f47,plain,(
% 1.70/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.70/0.58    inference(equality_resolution,[],[f40])).
% 1.70/0.58  fof(f40,plain,(
% 1.70/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.70/0.58    inference(cnf_transformation,[],[f25])).
% 1.70/0.58  fof(f25,plain,(
% 1.70/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK7(X0,X1,X2),X1) & ~r2_hidden(sK7(X0,X1,X2),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.70/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f24])).
% 1.70/0.58  fof(f24,plain,(
% 1.70/0.58    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK7(X0,X1,X2),X1) & ~r2_hidden(sK7(X0,X1,X2),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f23,plain,(
% 1.70/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.70/0.58    inference(rectify,[],[f22])).
% 1.70/0.58  fof(f22,plain,(
% 1.70/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.70/0.58    inference(flattening,[],[f21])).
% 1.70/0.58  fof(f21,plain,(
% 1.70/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.70/0.58    inference(nnf_transformation,[],[f1])).
% 1.70/0.58  fof(f1,axiom,(
% 1.70/0.58    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.70/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.70/0.58  fof(f90,plain,(
% 1.70/0.58    ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) | spl9_2),
% 1.70/0.58    inference(avatar_component_clause,[],[f89])).
% 1.70/0.58  fof(f1088,plain,(
% 1.70/0.58    ~spl9_16 | spl9_2),
% 1.70/0.58    inference(avatar_split_clause,[],[f271,f89,f256])).
% 1.70/0.58  fof(f271,plain,(
% 1.70/0.58    ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | spl9_2),
% 1.70/0.58    inference(resolution,[],[f90,f48])).
% 1.70/0.58  fof(f48,plain,(
% 1.70/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 1.70/0.58    inference(equality_resolution,[],[f39])).
% 1.70/0.58  fof(f39,plain,(
% 1.70/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.70/0.58    inference(cnf_transformation,[],[f25])).
% 1.70/0.58  fof(f1085,plain,(
% 1.70/0.58    ~spl9_13 | ~spl9_15 | spl9_17),
% 1.70/0.58    inference(avatar_split_clause,[],[f1070,f260,f240,f191])).
% 1.70/0.58  fof(f191,plain,(
% 1.70/0.58    spl9_13 <=> r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK1)),
% 1.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.70/0.58  fof(f1070,plain,(
% 1.70/0.58    ~r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK1) | (~spl9_15 | spl9_17)),
% 1.70/0.58    inference(resolution,[],[f241,f261])).
% 1.70/0.58  fof(f261,plain,(
% 1.70/0.58    ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) | spl9_17),
% 1.70/0.58    inference(avatar_component_clause,[],[f260])).
% 1.70/0.58  fof(f960,plain,(
% 1.70/0.58    ~spl9_17 | ~spl9_5),
% 1.70/0.58    inference(avatar_split_clause,[],[f957,f103,f260])).
% 1.70/0.58  fof(f103,plain,(
% 1.70/0.58    spl9_5 <=> ! [X0] : (~r2_hidden(X0,k2_xboole_0(sK0,sK1)) | ~r2_hidden(k4_tarski(X0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2))),
% 1.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.70/0.58  fof(f957,plain,(
% 1.70/0.58    ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) | ~spl9_5),
% 1.70/0.58    inference(duplicate_literal_removal,[],[f944])).
% 1.70/0.58  fof(f944,plain,(
% 1.70/0.58    ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) | ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) | ~spl9_5),
% 1.70/0.58    inference(resolution,[],[f282,f70])).
% 1.70/0.58  fof(f70,plain,(
% 1.70/0.58    ( ! [X4,X5,X3] : (r2_hidden(sK6(X3,X4,sK2),k2_xboole_0(X5,X4)) | ~r2_hidden(X3,k9_relat_1(sK2,X4))) )),
% 1.70/0.58    inference(resolution,[],[f61,f47])).
% 1.70/0.58  fof(f61,plain,(
% 1.70/0.58    ( ! [X4,X5] : (r2_hidden(sK6(X4,X5,sK2),X5) | ~r2_hidden(X4,k9_relat_1(sK2,X5))) )),
% 1.70/0.58    inference(resolution,[],[f26,f36])).
% 1.70/0.58  fof(f36,plain,(
% 1.70/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f20])).
% 1.70/0.58  fof(f20,plain,(
% 1.70/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.70/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f19])).
% 1.70/0.58  fof(f19,plain,(
% 1.70/0.58    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f18,plain,(
% 1.70/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.70/0.58    inference(rectify,[],[f17])).
% 1.70/0.58  fof(f17,plain,(
% 1.70/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.70/0.58    inference(nnf_transformation,[],[f8])).
% 1.70/0.58  fof(f8,plain,(
% 1.70/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.70/0.58    inference(ennf_transformation,[],[f3])).
% 1.70/0.58  fof(f3,axiom,(
% 1.70/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.70/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.70/0.58  fof(f26,plain,(
% 1.70/0.58    v1_relat_1(sK2)),
% 1.70/0.58    inference(cnf_transformation,[],[f10])).
% 1.70/0.58  fof(f10,plain,(
% 1.70/0.58    k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 1.70/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).
% 1.70/0.58  fof(f9,plain,(
% 1.70/0.58    ? [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_relat_1(X2)) => (k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f6,plain,(
% 1.70/0.58    ? [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 1.70/0.58    inference(ennf_transformation,[],[f5])).
% 1.70/0.58  fof(f5,negated_conjecture,(
% 1.70/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 1.70/0.58    inference(negated_conjecture,[],[f4])).
% 1.70/0.58  fof(f4,conjecture,(
% 1.70/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 1.70/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
% 1.70/0.58  fof(f282,plain,(
% 1.70/0.58    ( ! [X0] : (~r2_hidden(sK6(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),X0,sK2),k2_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,X0))) ) | ~spl9_5),
% 1.70/0.58    inference(resolution,[],[f104,f60])).
% 1.70/0.58  fof(f60,plain,(
% 1.70/0.58    ( ! [X2,X3] : (r2_hidden(k4_tarski(sK6(X2,X3,sK2),X2),sK2) | ~r2_hidden(X2,k9_relat_1(sK2,X3))) )),
% 1.70/0.58    inference(resolution,[],[f26,f35])).
% 1.70/0.58  fof(f35,plain,(
% 1.70/0.58    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f20])).
% 1.70/0.58  fof(f104,plain,(
% 1.70/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2) | ~r2_hidden(X0,k2_xboole_0(sK0,sK1))) ) | ~spl9_5),
% 1.70/0.58    inference(avatar_component_clause,[],[f103])).
% 1.70/0.58  fof(f959,plain,(
% 1.70/0.58    ~spl9_16 | ~spl9_5),
% 1.70/0.58    inference(avatar_split_clause,[],[f958,f103,f256])).
% 1.70/0.58  fof(f958,plain,(
% 1.70/0.58    ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | ~spl9_5),
% 1.70/0.58    inference(duplicate_literal_removal,[],[f943])).
% 1.70/0.58  fof(f943,plain,(
% 1.70/0.58    ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | ~spl9_5),
% 1.70/0.58    inference(resolution,[],[f282,f69])).
% 1.70/0.58  fof(f69,plain,(
% 1.70/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,sK2),k2_xboole_0(X1,X2)) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) )),
% 1.70/0.58    inference(resolution,[],[f61,f48])).
% 1.70/0.58  fof(f448,plain,(
% 1.70/0.58    spl9_16 | spl9_17 | ~spl9_2),
% 1.70/0.58    inference(avatar_split_clause,[],[f248,f89,f260,f256])).
% 1.70/0.58  fof(f248,plain,(
% 1.70/0.58    r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | ~spl9_2),
% 1.70/0.58    inference(resolution,[],[f91,f49])).
% 1.70/0.58  fof(f49,plain,(
% 1.70/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 1.70/0.58    inference(equality_resolution,[],[f38])).
% 1.70/0.58  fof(f38,plain,(
% 1.70/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.70/0.58    inference(cnf_transformation,[],[f25])).
% 1.70/0.58  fof(f91,plain,(
% 1.70/0.58    r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) | ~spl9_2),
% 1.70/0.58    inference(avatar_component_clause,[],[f89])).
% 1.70/0.58  fof(f247,plain,(
% 1.70/0.58    spl9_2 | spl9_3),
% 1.70/0.58    inference(avatar_split_clause,[],[f217,f93,f89])).
% 1.70/0.58  fof(f93,plain,(
% 1.70/0.58    spl9_3 <=> r2_hidden(k4_tarski(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2)),
% 1.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.70/0.58  fof(f217,plain,(
% 1.70/0.58    r2_hidden(k4_tarski(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2) | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 1.70/0.58    inference(resolution,[],[f68,f51])).
% 1.70/0.58  fof(f51,plain,(
% 1.70/0.58    ~sQ8_eqProxy(k9_relat_1(sK2,k2_xboole_0(sK0,sK1)),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 1.70/0.58    inference(equality_proxy_replacement,[],[f27,f50])).
% 1.70/0.58  fof(f50,plain,(
% 1.70/0.58    ! [X1,X0] : (sQ8_eqProxy(X0,X1) <=> X0 = X1)),
% 1.70/0.58    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).
% 1.70/0.58  fof(f27,plain,(
% 1.70/0.58    k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.70/0.58    inference(cnf_transformation,[],[f10])).
% 1.70/0.58  fof(f68,plain,(
% 1.70/0.58    ( ! [X21,X22] : (sQ8_eqProxy(k9_relat_1(sK2,X21),X22) | r2_hidden(k4_tarski(sK4(sK2,X21,X22),sK3(sK2,X21,X22)),sK2) | r2_hidden(sK3(sK2,X21,X22),X22)) )),
% 1.70/0.58    inference(resolution,[],[f26,f54])).
% 1.70/0.58  fof(f54,plain,(
% 1.70/0.58    ( ! [X2,X0,X1] : (sQ8_eqProxy(k9_relat_1(X0,X1),X2) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 1.70/0.58    inference(equality_proxy_replacement,[],[f31,f50])).
% 1.70/0.58  fof(f31,plain,(
% 1.70/0.58    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f16])).
% 1.70/0.58  fof(f16,plain,(
% 1.70/0.58    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.70/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f12,f15,f14,f13])).
% 1.70/0.58  fof(f13,plain,(
% 1.70/0.58    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f14,plain,(
% 1.70/0.58    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f15,plain,(
% 1.70/0.58    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)))),
% 1.70/0.58    introduced(choice_axiom,[])).
% 1.70/0.58  fof(f12,plain,(
% 1.70/0.58    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.70/0.58    inference(rectify,[],[f11])).
% 1.70/0.58  fof(f11,plain,(
% 1.70/0.58    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.70/0.58    inference(nnf_transformation,[],[f7])).
% 1.70/0.58  fof(f7,plain,(
% 1.70/0.58    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 1.70/0.58    inference(ennf_transformation,[],[f2])).
% 1.70/0.58  fof(f2,axiom,(
% 1.70/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 1.70/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 1.70/0.58  fof(f246,plain,(
% 1.70/0.58    ~spl9_2 | spl9_5),
% 1.70/0.58    inference(avatar_split_clause,[],[f216,f103,f89])).
% 1.70/0.58  fof(f216,plain,(
% 1.70/0.58    ( ! [X0] : (~r2_hidden(X0,k2_xboole_0(sK0,sK1)) | ~r2_hidden(k4_tarski(X0,sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2) | ~r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) )),
% 1.70/0.58    inference(resolution,[],[f66,f51])).
% 1.70/0.58  fof(f66,plain,(
% 1.70/0.58    ( ! [X17,X18,X16] : (sQ8_eqProxy(k9_relat_1(sK2,X16),X17) | ~r2_hidden(X18,X16) | ~r2_hidden(k4_tarski(X18,sK3(sK2,X16,X17)),sK2) | ~r2_hidden(sK3(sK2,X16,X17),X17)) )),
% 1.70/0.58    inference(resolution,[],[f26,f52])).
% 1.70/0.58  fof(f52,plain,(
% 1.70/0.58    ( ! [X4,X2,X0,X1] : (sQ8_eqProxy(k9_relat_1(X0,X1),X2) | ~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 1.70/0.58    inference(equality_proxy_replacement,[],[f33,f50])).
% 1.70/0.58  fof(f33,plain,(
% 1.70/0.58    ( ! [X4,X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | ~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f16])).
% 1.70/0.58  fof(f243,plain,(
% 1.70/0.58    spl9_15 | ~spl9_3),
% 1.70/0.58    inference(avatar_split_clause,[],[f226,f93,f240])).
% 1.70/0.58  fof(f226,plain,(
% 1.70/0.58    ( ! [X1] : (~r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),X1) | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,X1))) ) | ~spl9_3),
% 1.70/0.58    inference(resolution,[],[f95,f63])).
% 1.70/0.58  fof(f63,plain,(
% 1.70/0.58    ( ! [X10,X11,X9] : (~r2_hidden(k4_tarski(X11,X9),sK2) | ~r2_hidden(X11,X10) | r2_hidden(X9,k9_relat_1(sK2,X10))) )),
% 1.70/0.58    inference(resolution,[],[f26,f44])).
% 1.70/0.58  fof(f44,plain,(
% 1.70/0.58    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 1.70/0.58    inference(equality_resolution,[],[f30])).
% 1.70/0.58  fof(f30,plain,(
% 1.70/0.58    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f16])).
% 1.70/0.58  fof(f95,plain,(
% 1.70/0.58    r2_hidden(k4_tarski(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK2) | ~spl9_3),
% 1.70/0.58    inference(avatar_component_clause,[],[f93])).
% 1.70/0.58  fof(f194,plain,(
% 1.70/0.58    spl9_12 | spl9_13 | ~spl9_4),
% 1.70/0.58    inference(avatar_split_clause,[],[f180,f98,f191,f187])).
% 1.70/0.58  fof(f98,plain,(
% 1.70/0.58    spl9_4 <=> r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(sK0,sK1))),
% 1.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.70/0.58  fof(f180,plain,(
% 1.70/0.58    r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK1) | r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK0) | ~spl9_4),
% 1.70/0.58    inference(resolution,[],[f100,f49])).
% 1.70/0.58  fof(f100,plain,(
% 1.70/0.58    r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(sK0,sK1)) | ~spl9_4),
% 1.70/0.58    inference(avatar_component_clause,[],[f98])).
% 1.70/0.58  fof(f107,plain,(
% 1.70/0.58    spl9_1),
% 1.70/0.58    inference(avatar_contradiction_clause,[],[f106])).
% 1.70/0.58  fof(f106,plain,(
% 1.70/0.58    $false | spl9_1),
% 1.70/0.58    inference(resolution,[],[f87,f26])).
% 1.70/0.58  fof(f87,plain,(
% 1.70/0.58    ~v1_relat_1(sK2) | spl9_1),
% 1.70/0.58    inference(avatar_component_clause,[],[f85])).
% 1.70/0.58  fof(f85,plain,(
% 1.70/0.58    spl9_1 <=> v1_relat_1(sK2)),
% 1.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.70/0.58  fof(f101,plain,(
% 1.70/0.58    ~spl9_1 | spl9_2 | spl9_4),
% 1.70/0.58    inference(avatar_split_clause,[],[f82,f98,f89,f85])).
% 1.70/0.58  fof(f82,plain,(
% 1.70/0.58    r2_hidden(sK4(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK2,k2_xboole_0(sK0,sK1),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) | ~v1_relat_1(sK2)),
% 1.70/0.58    inference(resolution,[],[f51,f53])).
% 1.70/0.58  fof(f53,plain,(
% 1.70/0.58    ( ! [X2,X0,X1] : (sQ8_eqProxy(k9_relat_1(X0,X1),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 1.70/0.58    inference(equality_proxy_replacement,[],[f32,f50])).
% 1.70/0.58  fof(f32,plain,(
% 1.70/0.58    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f16])).
% 1.70/0.58  % SZS output end Proof for theBenchmark
% 1.70/0.58  % (19844)------------------------------
% 1.70/0.58  % (19844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.58  % (19844)Termination reason: Refutation
% 1.70/0.58  
% 1.70/0.58  % (19844)Memory used [KB]: 7036
% 1.70/0.58  % (19844)Time elapsed: 0.155 s
% 1.70/0.58  % (19844)------------------------------
% 1.70/0.58  % (19844)------------------------------
% 1.70/0.58  % (19831)Success in time 0.217 s
%------------------------------------------------------------------------------
