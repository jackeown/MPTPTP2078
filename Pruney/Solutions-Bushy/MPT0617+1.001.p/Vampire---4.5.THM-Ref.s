%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0617+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 366 expanded)
%              Number of leaves         :   14 ( 122 expanded)
%              Depth                    :   16
%              Number of atoms          :  392 (2382 expanded)
%              Number of equality atoms :   83 ( 765 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f433,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f245,f247,f270,f371,f380,f429])).

fof(f429,plain,
    ( ~ spl7_7
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl7_7
    | spl7_15 ),
    inference(subsumption_resolution,[],[f427,f236])).

fof(f236,plain,
    ( sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl7_15
  <=> sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f427,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f424,f378])).

fof(f378,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f377,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != sK1
    & ! [X2] :
        ( k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2)
        | ~ r2_hidden(X2,k1_relat_1(sK0)) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) )
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & ! [X2] :
              ( k1_funct_1(X1,X2) = k1_funct_1(sK0,X2)
              | ~ r2_hidden(X2,k1_relat_1(sK0)) )
          & k1_relat_1(X1) = k1_relat_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( sK0 != X1
        & ! [X2] :
            ( k1_funct_1(X1,X2) = k1_funct_1(sK0,X2)
            | ~ r2_hidden(X2,k1_relat_1(sK0)) )
        & k1_relat_1(X1) = k1_relat_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != sK1
      & ! [X2] :
          ( k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2)
          | ~ r2_hidden(X2,k1_relat_1(sK0)) )
      & k1_relat_1(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2] :
                    ( r2_hidden(X2,k1_relat_1(X0))
                   => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f377,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f376,f26])).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f376,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f271,f272])).

fof(f272,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ spl7_7 ),
    inference(resolution,[],[f131,f49])).

fof(f49,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
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
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
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
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f131,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_7
  <=> r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f271,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl7_7 ),
    inference(resolution,[],[f131,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f424,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ spl7_7 ),
    inference(resolution,[],[f272,f30])).

fof(f30,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f380,plain,
    ( ~ spl7_7
    | spl7_16 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl7_7
    | spl7_16 ),
    inference(subsumption_resolution,[],[f241,f272])).

fof(f241,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl7_16
  <=> r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f371,plain,
    ( spl7_6
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl7_6
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f369,f126])).

fof(f126,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_6
  <=> r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f369,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(forward_demodulation,[],[f364,f237])).

fof(f237,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f235])).

fof(f364,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK1,sK2(sK0,sK1))),sK1)
    | ~ spl7_16 ),
    inference(resolution,[],[f240,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    inference(subsumption_resolution,[],[f60,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f59,f28])).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f48,f29])).

fof(f29,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f240,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f239])).

fof(f270,plain,
    ( ~ spl7_6
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f268,f25])).

fof(f268,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f267,f27])).

fof(f267,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f266,f263])).

fof(f263,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f262,f260])).

fof(f260,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f256,f237])).

fof(f256,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ spl7_6 ),
    inference(resolution,[],[f243,f30])).

fof(f243,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f230,f29])).

fof(f230,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ spl7_6 ),
    inference(resolution,[],[f127,f49])).

fof(f127,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f262,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f261,f25])).

fof(f261,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f257,f26])).

fof(f257,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl7_6 ),
    inference(resolution,[],[f243,f48])).

fof(f266,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f228,f31])).

fof(f31,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f228,plain,
    ( sK0 = sK1
    | ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl7_6 ),
    inference(resolution,[],[f127,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).

fof(f247,plain,
    ( ~ spl7_6
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f246])).

% (29672)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f246,plain,
    ( $false
    | ~ spl7_6
    | spl7_15 ),
    inference(global_subsumption,[],[f233,f243,f236])).

fof(f233,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f232,f29])).

fof(f232,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f231,f27])).

fof(f231,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f229,f28])).

fof(f229,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_6 ),
    inference(resolution,[],[f127,f37])).

fof(f245,plain,
    ( ~ spl7_6
    | spl7_16 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl7_6
    | spl7_16 ),
    inference(subsumption_resolution,[],[f241,f243])).

fof(f132,plain,
    ( spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f123,f129,f125])).

fof(f123,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f120,f31])).

fof(f120,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | sK0 = sK1
    | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) ),
    inference(resolution,[],[f90,f25])).

fof(f90,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK2(X1,sK1),sK3(X1,sK1)),X1)
      | sK1 = X1
      | r2_hidden(k4_tarski(sK2(X1,sK1),sK3(X1,sK1)),sK1) ) ),
    inference(resolution,[],[f34,f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
