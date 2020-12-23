%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 168 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  307 ( 783 expanded)
%              Number of equality atoms :   92 ( 236 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f66,f89,f105,f109,f121])).

fof(f121,plain,
    ( spl4_5
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f119,f76])).

fof(f76,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_5
  <=> r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f119,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f118,f45])).

fof(f45,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
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

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f118,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0))
    | r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | ~ spl4_7 ),
    inference(superposition,[],[f35,f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f109,plain,
    ( spl4_1
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl4_1
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f107,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ( k1_xboole_0 != sK1
        & r2_hidden(sK1,k2_relat_1(sK0)) )
      | ~ v3_relat_1(sK0) )
    & ( ! [X2] :
          ( k1_xboole_0 = X2
          | ~ r2_hidden(X2,k2_relat_1(sK0)) )
      | v3_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( k1_xboole_0 != X1
              & r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v3_relat_1(X0) )
        & ( ! [X2] :
              ( k1_xboole_0 = X2
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
          | v3_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(sK0)) )
        | ~ v3_relat_1(sK0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(sK0)) )
        | v3_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & r2_hidden(X1,k2_relat_1(sK0)) )
   => ( k1_xboole_0 != sK1
      & r2_hidden(sK1,k2_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

fof(f107,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_1
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f106,f52])).

fof(f52,plain,
    ( ~ v3_relat_1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_1
  <=> v3_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f106,plain,
    ( v3_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f77,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_tarski(k1_xboole_0,k1_xboole_0))
      | v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0] :
      ( v3_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v3_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
        & ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
          | ~ v3_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

fof(f77,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f105,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f103,f56])).

fof(f56,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f100,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f100,plain,
    ( r2_hidden(sK1,k2_tarski(k1_xboole_0,k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f96,f94])).

fof(f94,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f90,f26])).

fof(f90,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f51,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v3_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k2_tarski(k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f31,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,
    ( v3_relat_1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | r2_hidden(sK1,X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f61,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_3
  <=> r2_hidden(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,
    ( spl4_1
    | spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f84,f64,f86,f50])).

fof(f64,plain,
    ( spl4_4
  <=> ! [X2] :
        ( k1_xboole_0 = X2
        | ~ r2_hidden(X2,k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f84,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | v3_relat_1(sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f69,f26])).

fof(f69,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))
    | v3_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f67,f42])).

fof(f67,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(sK0),X0)
        | k1_xboole_0 = sK2(k2_relat_1(sK0),X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f65,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK0))
        | k1_xboole_0 = X2 )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,
    ( spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f27,f64,f50])).

fof(f27,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | ~ r2_hidden(X2,k2_relat_1(sK0))
      | v3_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f28,f59,f50])).

fof(f28,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f29,f54,f50])).

fof(f29,plain,
    ( k1_xboole_0 != sK1
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (15506)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (15500)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (15506)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f57,f62,f66,f89,f105,f109,f121])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    spl4_5 | ~spl4_7),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f120])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    $false | (spl4_5 | ~spl4_7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f119,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ~r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    spl4_5 <=> r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | ~spl4_7),
% 0.20/0.51    inference(subsumption_resolution,[],[f118,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.20/0.51    inference(equality_resolution,[],[f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.20/0.51    inference(equality_resolution,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.51    inference(rectify,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ~r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) | r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | ~spl4_7),
% 0.20/0.51    inference(superposition,[],[f35,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    k1_xboole_0 = sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | ~spl4_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl4_7 <=> k1_xboole_0 = sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    spl4_1 | ~spl4_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    $false | (spl4_1 | ~spl4_5)),
% 0.20/0.51    inference(subsumption_resolution,[],[f107,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ((k1_xboole_0 != sK1 & r2_hidden(sK1,k2_relat_1(sK0))) | ~v3_relat_1(sK0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0))) | v3_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14,f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0)) => ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(sK0))) | ~v3_relat_1(sK0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0))) | v3_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(sK0))) => (k1_xboole_0 != sK1 & r2_hidden(sK1,k2_relat_1(sK0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0))),
% 0.20/0.51    inference(rectify,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0] : (((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0))) | v3_relat_1(X0))) & v1_relat_1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0] : ((v3_relat_1(X0) <~> ! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0)))) & v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.20/0.51    inference(negated_conjecture,[],[f5])).
% 0.20/0.51  fof(f5,conjecture,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ~v1_relat_1(sK0) | (spl4_1 | ~spl4_5)),
% 0.20/0.51    inference(subsumption_resolution,[],[f106,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ~v3_relat_1(sK0) | spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl4_1 <=> v3_relat_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    v3_relat_1(sK0) | ~v1_relat_1(sK0) | ~spl4_5),
% 0.20/0.51    inference(resolution,[],[f77,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_tarski(k1_xboole_0,k1_xboole_0)) | v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f32,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0] : (v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (((v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) & (r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0] : ((v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | ~spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f75])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ~spl4_1 | spl4_2 | ~spl4_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f104])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    $false | (~spl4_1 | spl4_2 | ~spl4_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f103,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl4_2 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | (~spl4_1 | ~spl4_3)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | (~spl4_1 | ~spl4_3)),
% 0.20/0.51    inference(resolution,[],[f100,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.20/0.51    inference(equality_resolution,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    r2_hidden(sK1,k2_tarski(k1_xboole_0,k1_xboole_0)) | (~spl4_1 | ~spl4_3)),
% 0.20/0.51    inference(resolution,[],[f96,f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | ~spl4_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f90,f26])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    r1_tarski(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(sK0) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f51,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0] : (~v3_relat_1(X0) | r1_tarski(k2_relat_1(X0),k2_tarski(k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f31,f30])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    v3_relat_1(sK0) | ~spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f50])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r2_hidden(sK1,X0)) ) | ~spl4_3),
% 0.20/0.51    inference(resolution,[],[f61,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    r2_hidden(sK1,k2_relat_1(sK0)) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl4_3 <=> r2_hidden(sK1,k2_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl4_1 | spl4_7 | ~spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f84,f64,f86,f50])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl4_4 <=> ! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    k1_xboole_0 = sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | v3_relat_1(sK0) | ~spl4_4),
% 0.20/0.51    inference(subsumption_resolution,[],[f69,f26])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    k1_xboole_0 = sK2(k2_relat_1(sK0),k2_tarski(k1_xboole_0,k1_xboole_0)) | v3_relat_1(sK0) | ~v1_relat_1(sK0) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f67,f42])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k2_relat_1(sK0),X0) | k1_xboole_0 = sK2(k2_relat_1(sK0),X0)) ) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f65,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK0)) | k1_xboole_0 = X2) ) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f64])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl4_1 | spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f27,f64,f50])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0)) | v3_relat_1(sK0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ~spl4_1 | spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f28,f59,f50])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    r2_hidden(sK1,k2_relat_1(sK0)) | ~v3_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ~spl4_1 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f29,f54,f50])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | ~v3_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (15506)------------------------------
% 0.20/0.51  % (15506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15506)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (15506)Memory used [KB]: 10746
% 0.20/0.51  % (15506)Time elapsed: 0.099 s
% 0.20/0.51  % (15506)------------------------------
% 0.20/0.51  % (15506)------------------------------
% 0.20/0.51  % (15510)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (15497)Success in time 0.157 s
%------------------------------------------------------------------------------
