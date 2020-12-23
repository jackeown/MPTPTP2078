%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0611+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:18 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 110 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  222 ( 435 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f49,f53,f62,f96])).

fof(f96,plain,
    ( spl8_5
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f94,f51,f47,f60])).

fof(f60,plain,
    ( spl8_5
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f47,plain,
    ( spl8_2
  <=> r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f51,plain,
    ( spl8_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f94,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,
    ( r1_xboole_0(sK1,sK0)
    | r1_xboole_0(sK1,sK0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f90,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,X0),sK0)
        | r1_xboole_0(sK1,X0) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f89,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f52])).

fof(f52,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f81,f52])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,X2)
        | ~ v1_relat_1(X2) )
    | ~ spl8_2 ),
    inference(resolution,[],[f80,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f40,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_tarski(sK2(X1),sK3(X1)) = X1
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tarski(sK2(X1),sK3(X1)) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f17])).

fof(f17,plain,(
    ! [X1] :
      ( ? [X2,X3] : k4_tarski(X2,X3) = X1
     => k4_tarski(sK2(X1),sK3(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f40,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f25,f24,f23])).

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(X0),k2_relat_1(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_2 ),
    inference(resolution,[],[f79,f64])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f34,f48])).

fof(f48,plain,
    ( r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,
    ( ~ spl8_5
    | spl8_1 ),
    inference(avatar_split_clause,[],[f58,f43,f60])).

fof(f43,plain,
    ( spl8_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f58,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl8_1 ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f53,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f28,f51])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

fof(f49,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f29,f47])).

fof(f29,plain,(
    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f30,f43])).

fof(f30,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
