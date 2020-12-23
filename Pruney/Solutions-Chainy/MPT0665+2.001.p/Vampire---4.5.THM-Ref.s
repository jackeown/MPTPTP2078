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
% DateTime   : Thu Dec  3 12:53:16 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 106 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  301 ( 495 expanded)
%              Number of equality atoms :   35 (  35 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f125,f180,f207,f230,f442,f473])).

fof(f473,plain,(
    spl13_35 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | spl13_35 ),
    inference(resolution,[],[f440,f43])).

fof(f43,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    & r2_hidden(sK0,sK1)
    & r2_hidden(sK0,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
        & r2_hidden(X0,X1)
        & r2_hidden(X0,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
      & r2_hidden(sK0,sK1)
      & r2_hidden(sK0,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X0,X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
         => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

fof(f440,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl13_35 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl13_35
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).

fof(f442,plain,
    ( ~ spl13_3
    | ~ spl13_1
    | ~ spl13_9
    | ~ spl13_35
    | ~ spl13_15 ),
    inference(avatar_split_clause,[],[f430,f205,f438,f166,f100,f109])).

fof(f109,plain,
    ( spl13_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f100,plain,
    ( spl13_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f166,plain,
    ( spl13_9
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f205,plain,
    ( spl13_15
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK2,sK0)),sK2)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f430,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl13_15 ),
    inference(resolution,[],[f206,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f206,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK2,sK0)),sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl13_15 ),
    inference(avatar_component_clause,[],[f205])).

fof(f230,plain,(
    spl13_14 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl13_14 ),
    inference(resolution,[],[f203,f90])).

fof(f90,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f40,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f203,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl13_14 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl13_14
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f207,plain,
    ( ~ spl13_3
    | ~ spl13_14
    | spl13_15 ),
    inference(avatar_split_clause,[],[f195,f205,f201,f109])).

fof(f195,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK2,sK0)),sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ v1_relat_1(k7_relat_1(sK2,sK1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f120,f68])).

fof(f68,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK3(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                    & r2_hidden(sK3(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f120,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f44,f74])).

fof(f74,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f44,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f180,plain,(
    spl13_9 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl13_9 ),
    inference(resolution,[],[f168,f42])).

fof(f42,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f168,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl13_9 ),
    inference(avatar_component_clause,[],[f166])).

fof(f125,plain,(
    spl13_3 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl13_3 ),
    inference(resolution,[],[f111,f40])).

fof(f111,plain,
    ( ~ v1_relat_1(sK2)
    | spl13_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f123,plain,(
    spl13_1 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl13_1 ),
    inference(resolution,[],[f102,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,
    ( ~ v1_funct_1(sK2)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : run_vampire %s %d
% 0.08/0.28  % Computer   : n005.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 12:25:17 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.14/0.36  % (7215)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.14/0.37  % (7215)Refutation found. Thanks to Tanya!
% 0.14/0.37  % SZS status Theorem for theBenchmark
% 0.14/0.37  % (7220)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.14/0.38  % SZS output start Proof for theBenchmark
% 0.14/0.38  fof(f474,plain,(
% 0.14/0.38    $false),
% 0.14/0.38    inference(avatar_sat_refutation,[],[f123,f125,f180,f207,f230,f442,f473])).
% 0.14/0.38  fof(f473,plain,(
% 0.14/0.38    spl13_35),
% 0.14/0.38    inference(avatar_contradiction_clause,[],[f471])).
% 0.14/0.38  fof(f471,plain,(
% 0.14/0.38    $false | spl13_35),
% 0.14/0.38    inference(resolution,[],[f440,f43])).
% 0.14/0.38  fof(f43,plain,(
% 0.14/0.38    r2_hidden(sK0,sK1)),
% 0.14/0.38    inference(cnf_transformation,[],[f17])).
% 0.14/0.38  fof(f17,plain,(
% 0.14/0.38    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) & r2_hidden(sK0,sK1) & r2_hidden(sK0,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.14/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).
% 0.14/0.38  fof(f16,plain,(
% 0.14/0.38    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) & r2_hidden(sK0,sK1) & r2_hidden(sK0,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.14/0.38    introduced(choice_axiom,[])).
% 0.14/0.38  fof(f10,plain,(
% 0.14/0.38    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.14/0.38    inference(flattening,[],[f9])).
% 0.14/0.38  fof(f9,plain,(
% 0.14/0.38    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & (r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.14/0.38    inference(ennf_transformation,[],[f8])).
% 0.14/0.38  fof(f8,negated_conjecture,(
% 0.14/0.38    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.14/0.38    inference(negated_conjecture,[],[f7])).
% 0.14/0.38  fof(f7,conjecture,(
% 0.14/0.38    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.14/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).
% 0.14/0.38  fof(f440,plain,(
% 0.14/0.38    ~r2_hidden(sK0,sK1) | spl13_35),
% 0.14/0.38    inference(avatar_component_clause,[],[f438])).
% 0.14/0.38  fof(f438,plain,(
% 0.14/0.38    spl13_35 <=> r2_hidden(sK0,sK1)),
% 0.14/0.38    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).
% 0.14/0.38  fof(f442,plain,(
% 0.14/0.38    ~spl13_3 | ~spl13_1 | ~spl13_9 | ~spl13_35 | ~spl13_15),
% 0.14/0.38    inference(avatar_split_clause,[],[f430,f205,f438,f166,f100,f109])).
% 0.14/0.38  fof(f109,plain,(
% 0.14/0.38    spl13_3 <=> v1_relat_1(sK2)),
% 0.14/0.38    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 0.14/0.38  fof(f100,plain,(
% 0.14/0.38    spl13_1 <=> v1_funct_1(sK2)),
% 0.14/0.38    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 0.14/0.38  fof(f166,plain,(
% 0.14/0.38    spl13_9 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.14/0.38    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 0.14/0.38  fof(f205,plain,(
% 0.14/0.38    spl13_15 <=> ! [X0] : (~r2_hidden(k4_tarski(X0,k1_funct_1(sK2,sK0)),sK2) | ~r2_hidden(X0,sK1))),
% 0.14/0.38    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 0.14/0.38  fof(f430,plain,(
% 0.14/0.38    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl13_15),
% 0.14/0.38    inference(resolution,[],[f206,f73])).
% 0.14/0.38  fof(f73,plain,(
% 0.14/0.38    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.14/0.38    inference(equality_resolution,[],[f51])).
% 0.14/0.38  fof(f51,plain,(
% 0.14/0.38    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.14/0.38    inference(cnf_transformation,[],[f23])).
% 0.14/0.38  fof(f23,plain,(
% 0.14/0.38    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.14/0.38    inference(nnf_transformation,[],[f13])).
% 0.14/0.38  fof(f13,plain,(
% 0.14/0.38    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.14/0.38    inference(flattening,[],[f12])).
% 0.14/0.38  fof(f12,plain,(
% 0.14/0.38    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.14/0.38    inference(ennf_transformation,[],[f6])).
% 0.14/0.38  fof(f6,axiom,(
% 0.14/0.38    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.14/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.14/0.38  fof(f206,plain,(
% 0.14/0.38    ( ! [X0] : (~r2_hidden(k4_tarski(X0,k1_funct_1(sK2,sK0)),sK2) | ~r2_hidden(X0,sK1)) ) | ~spl13_15),
% 0.14/0.38    inference(avatar_component_clause,[],[f205])).
% 0.14/0.38  fof(f230,plain,(
% 0.14/0.38    spl13_14),
% 0.14/0.38    inference(avatar_contradiction_clause,[],[f228])).
% 0.14/0.38  fof(f228,plain,(
% 0.14/0.38    $false | spl13_14),
% 0.14/0.38    inference(resolution,[],[f203,f90])).
% 0.14/0.38  fof(f90,plain,(
% 0.14/0.38    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.14/0.38    inference(resolution,[],[f40,f55])).
% 0.14/0.38  fof(f55,plain,(
% 0.14/0.38    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.14/0.38    inference(cnf_transformation,[],[f14])).
% 0.14/0.38  fof(f14,plain,(
% 0.14/0.38    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.14/0.38    inference(ennf_transformation,[],[f4])).
% 0.14/0.38  fof(f4,axiom,(
% 0.14/0.38    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.14/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.14/0.38  fof(f40,plain,(
% 0.14/0.38    v1_relat_1(sK2)),
% 0.14/0.38    inference(cnf_transformation,[],[f17])).
% 0.14/0.38  fof(f203,plain,(
% 0.14/0.38    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl13_14),
% 0.14/0.38    inference(avatar_component_clause,[],[f201])).
% 0.14/0.38  fof(f201,plain,(
% 0.14/0.38    spl13_14 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.14/0.38    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 0.14/0.38  fof(f207,plain,(
% 0.14/0.38    ~spl13_3 | ~spl13_14 | spl13_15),
% 0.14/0.38    inference(avatar_split_clause,[],[f195,f205,f201,f109])).
% 0.14/0.38  fof(f195,plain,(
% 0.14/0.38    ( ! [X0] : (~r2_hidden(k4_tarski(X0,k1_funct_1(sK2,sK0)),sK2) | ~r2_hidden(X0,sK1) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2)) )),
% 0.14/0.38    inference(resolution,[],[f120,f68])).
% 0.14/0.38  fof(f68,plain,(
% 0.14/0.38    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.14/0.38    inference(equality_resolution,[],[f47])).
% 0.14/0.38  fof(f47,plain,(
% 0.14/0.38    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.14/0.38    inference(cnf_transformation,[],[f22])).
% 0.14/0.38  fof(f22,plain,(
% 0.14/0.38    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.14/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f21])).
% 0.14/0.39  fof(f21,plain,(
% 0.14/0.39    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.14/0.39    introduced(choice_axiom,[])).
% 0.14/0.39  fof(f20,plain,(
% 0.14/0.39    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.14/0.39    inference(rectify,[],[f19])).
% 0.14/0.39  fof(f19,plain,(
% 0.14/0.39    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.14/0.39    inference(flattening,[],[f18])).
% 0.14/0.39  fof(f18,plain,(
% 0.14/0.39    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.14/0.39    inference(nnf_transformation,[],[f11])).
% 0.14/0.39  fof(f11,plain,(
% 0.14/0.39    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.14/0.39    inference(ennf_transformation,[],[f1])).
% 0.14/0.39  fof(f1,axiom,(
% 0.14/0.39    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.14/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 0.14/0.39  fof(f120,plain,(
% 0.14/0.39    ( ! [X0] : (~r2_hidden(k4_tarski(X0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1))) )),
% 0.14/0.39    inference(resolution,[],[f44,f74])).
% 0.14/0.39  fof(f74,plain,(
% 0.14/0.39    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.14/0.39    inference(equality_resolution,[],[f57])).
% 0.14/0.39  fof(f57,plain,(
% 0.14/0.39    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.14/0.39    inference(cnf_transformation,[],[f29])).
% 0.14/0.39  fof(f29,plain,(
% 0.14/0.39    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.14/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f25,f28,f27,f26])).
% 0.14/0.39  fof(f26,plain,(
% 0.14/0.39    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.14/0.39    introduced(choice_axiom,[])).
% 0.14/0.39  fof(f27,plain,(
% 0.14/0.39    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 0.14/0.39    introduced(choice_axiom,[])).
% 0.14/0.39  fof(f28,plain,(
% 0.14/0.39    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 0.14/0.39    introduced(choice_axiom,[])).
% 0.14/0.39  fof(f25,plain,(
% 0.14/0.39    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.14/0.39    inference(rectify,[],[f24])).
% 0.14/0.39  fof(f24,plain,(
% 0.14/0.39    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.14/0.39    inference(nnf_transformation,[],[f3])).
% 0.14/0.39  fof(f3,axiom,(
% 0.14/0.39    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.14/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.14/0.39  fof(f44,plain,(
% 0.14/0.39    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))),
% 0.14/0.39    inference(cnf_transformation,[],[f17])).
% 0.14/0.39  fof(f180,plain,(
% 0.14/0.39    spl13_9),
% 0.14/0.39    inference(avatar_contradiction_clause,[],[f177])).
% 0.14/0.39  fof(f177,plain,(
% 0.14/0.39    $false | spl13_9),
% 0.14/0.39    inference(resolution,[],[f168,f42])).
% 0.14/0.39  fof(f42,plain,(
% 0.14/0.39    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.14/0.39    inference(cnf_transformation,[],[f17])).
% 0.14/0.39  fof(f168,plain,(
% 0.14/0.39    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl13_9),
% 0.14/0.39    inference(avatar_component_clause,[],[f166])).
% 0.14/0.39  fof(f125,plain,(
% 0.14/0.39    spl13_3),
% 0.14/0.39    inference(avatar_contradiction_clause,[],[f124])).
% 0.14/0.39  fof(f124,plain,(
% 0.14/0.39    $false | spl13_3),
% 0.14/0.39    inference(resolution,[],[f111,f40])).
% 0.14/0.39  fof(f111,plain,(
% 0.14/0.39    ~v1_relat_1(sK2) | spl13_3),
% 0.14/0.39    inference(avatar_component_clause,[],[f109])).
% 0.14/0.39  fof(f123,plain,(
% 0.14/0.39    spl13_1),
% 0.14/0.39    inference(avatar_contradiction_clause,[],[f122])).
% 0.14/0.39  fof(f122,plain,(
% 0.14/0.39    $false | spl13_1),
% 0.14/0.39    inference(resolution,[],[f102,f41])).
% 0.14/0.39  fof(f41,plain,(
% 0.14/0.39    v1_funct_1(sK2)),
% 0.14/0.39    inference(cnf_transformation,[],[f17])).
% 0.14/0.39  fof(f102,plain,(
% 0.14/0.39    ~v1_funct_1(sK2) | spl13_1),
% 0.14/0.39    inference(avatar_component_clause,[],[f100])).
% 0.14/0.39  % SZS output end Proof for theBenchmark
% 0.14/0.39  % (7215)------------------------------
% 0.14/0.39  % (7215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.39  % (7215)Termination reason: Refutation
% 0.14/0.39  
% 0.14/0.39  % (7215)Memory used [KB]: 6396
% 0.14/0.39  % (7215)Time elapsed: 0.042 s
% 0.14/0.39  % (7215)------------------------------
% 0.14/0.39  % (7215)------------------------------
% 0.14/0.39  % (7199)Success in time 0.097 s
%------------------------------------------------------------------------------
