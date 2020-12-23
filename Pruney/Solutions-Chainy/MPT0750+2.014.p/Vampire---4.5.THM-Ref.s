%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:41 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 449 expanded)
%              Number of leaves         :   27 ( 144 expanded)
%              Depth                    :   15
%              Number of atoms          :  515 (2274 expanded)
%              Number of equality atoms :   32 ( 126 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f116,f163,f261,f465,f498,f1224])).

fof(f1224,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f1223])).

fof(f1223,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f1222,f856])).

fof(f856,plain,
    ( r1_ordinal1(sK0,sK5(sK0,sK1))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f850,f617])).

fof(f617,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f101,f526,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f75,f55])).

fof(f55,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f526,plain,
    ( r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f49,f165,f505,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f505,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f111,f49,f106,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f57,f55])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f106,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f111,plain,
    ( v3_ordinal1(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f165,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f111,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f56,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f49,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
        & r2_hidden(sK1,sK0)
        & v3_ordinal1(sK1) )
      | ~ v4_ordinal1(sK0) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK0)
          | ~ r2_hidden(X2,sK0)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK0) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | v4_ordinal1(X0) )
        & v3_ordinal1(X0) )
   => ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),sK0)
            & r2_hidden(X1,sK0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK0)
            | ~ r2_hidden(X2,sK0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK0) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ~ r2_hidden(k1_ordinal1(X1),sK0)
        & r2_hidden(X1,sK0)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
      & r2_hidden(sK1,sK0)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),X0)
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f101,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_2
  <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f850,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK5(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f111,f582,f782,f84])).

fof(f782,plain,
    ( v3_ordinal1(sK5(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f49,f578,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f578,plain,
    ( r2_hidden(sK5(sK0,sK1),sK0)
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f106,f521])).

fof(f521,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK0)
        | r2_hidden(sK5(sK0,X6),sK0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f91,f499])).

fof(f499,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f96,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

fof(f96,plain,
    ( v4_ordinal1(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_1
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f91,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK3(X0,X1),X3) )
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( ( r2_hidden(sK4(X0,X1),X0)
              & r2_hidden(sK3(X0,X1),sK4(X0,X1)) )
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK5(X0,X5),X0)
                & r2_hidden(X5,sK5(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f42,f45,f44,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK3(X0,X1),X3) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK3(X0,X1),X4) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK3(X0,X1),X4) )
     => ( r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK5(X0,X5),X0)
        & r2_hidden(X5,sK5(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f582,plain,
    ( r2_hidden(sK1,sK5(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f106,f522])).

fof(f522,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK0)
        | r2_hidden(X7,sK5(sK0,X7)) )
    | ~ spl6_1 ),
    inference(superposition,[],[f92,f499])).

fof(f92,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK5(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK5(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1222,plain,
    ( ~ r1_ordinal1(sK0,sK5(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f49,f782,f784,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f784,plain,
    ( ~ r1_tarski(sK0,sK5(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f578,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f498,plain,
    ( spl6_1
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | spl6_1
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f496,f471])).

fof(f471,plain,
    ( ~ r2_hidden(k2_xboole_0(sK3(sK0,sK0),k1_tarski(sK3(sK0,sK0))),sK0)
    | spl6_1
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f180,f81,f158,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK3(X0,X1),X3)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f158,plain,
    ( r2_hidden(sK3(sK0,sK0),sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl6_6
  <=> r2_hidden(sK3(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f81,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f54,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f180,plain,
    ( sK0 != k3_tarski(sK0)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f97,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,
    ( ~ v4_ordinal1(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f496,plain,
    ( r2_hidden(k2_xboole_0(sK3(sK0,sK0),k1_tarski(sK3(sK0,sK0))),sK0)
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f158,f473,f115])).

fof(f115,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_5
  <=> ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f473,plain,
    ( v3_ordinal1(sK3(sK0,sK0))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f49,f158,f63])).

fof(f465,plain,
    ( spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f455,f426])).

fof(f426,plain,
    ( ~ r1_ordinal1(sK4(sK0,sK0),sK0)
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f49,f283,f298,f64])).

fof(f298,plain,
    ( ~ r1_tarski(sK4(sK0,sK0),sK0)
    | spl6_6
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f157,f260,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f260,plain,
    ( r2_hidden(sK3(sK0,sK0),sK4(sK0,sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl6_8
  <=> r2_hidden(sK3(sK0,sK0),sK4(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f157,plain,
    ( ~ r2_hidden(sK3(sK0,sK0),sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f283,plain,
    ( v3_ordinal1(sK4(sK0,sK0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f49,f162,f63])).

fof(f162,plain,
    ( r2_hidden(sK4(sK0,sK0),sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_7
  <=> r2_hidden(sK4(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f455,plain,
    ( r1_ordinal1(sK4(sK0,sK0),sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f49,f283,f286,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f59,f55])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f286,plain,
    ( r2_hidden(sK4(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f162,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f55])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f261,plain,
    ( spl6_6
    | spl6_8
    | spl6_1 ),
    inference(avatar_split_clause,[],[f256,f95,f258,f156])).

fof(f256,plain,
    ( r2_hidden(sK3(sK0,sK0),sK4(sK0,sK0))
    | r2_hidden(sK3(sK0,sK0),sK0)
    | spl6_1 ),
    inference(equality_resolution,[],[f192])).

fof(f192,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK3(sK0,X0),sK4(sK0,X0))
        | r2_hidden(sK3(sK0,X0),X0) )
    | spl6_1 ),
    inference(superposition,[],[f180,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK3(X0,X1),sK4(X0,X1))
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f163,plain,
    ( spl6_6
    | spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f154,f95,f160,f156])).

fof(f154,plain,
    ( r2_hidden(sK4(sK0,sK0),sK0)
    | r2_hidden(sK3(sK0,sK0),sK0)
    | spl6_1 ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,
    ( ! [X1] :
        ( sK0 != X1
        | r2_hidden(sK4(sK0,X1),sK0)
        | r2_hidden(sK3(sK0,X1),X1) )
    | spl6_1 ),
    inference(superposition,[],[f122,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK4(X0,X1),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f122,plain,
    ( sK0 != k3_tarski(sK0)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f97,f62])).

fof(f116,plain,
    ( spl6_1
    | spl6_5 ),
    inference(avatar_split_clause,[],[f80,f114,f95])).

fof(f80,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f50,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f112,plain,
    ( ~ spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f51,f109,f95])).

fof(f51,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f107,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f52,f104,f95])).

fof(f52,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f79,f99,f95])).

fof(f79,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f53,f55])).

fof(f53,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:03:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (14511)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (14512)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (14524)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (14516)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (14499)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (14505)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (14501)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (14502)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (14518)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.54  % (14507)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.54  % (14507)Refutation not found, incomplete strategy% (14507)------------------------------
% 1.38/0.54  % (14507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (14507)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (14507)Memory used [KB]: 10746
% 1.38/0.54  % (14507)Time elapsed: 0.137 s
% 1.38/0.54  % (14507)------------------------------
% 1.38/0.54  % (14507)------------------------------
% 1.38/0.54  % (14526)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.54  % (14523)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.54  % (14517)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.55  % (14503)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.55  % (14498)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.55  % (14523)Refutation not found, incomplete strategy% (14523)------------------------------
% 1.38/0.55  % (14523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (14523)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (14523)Memory used [KB]: 10746
% 1.38/0.55  % (14523)Time elapsed: 0.135 s
% 1.38/0.55  % (14523)------------------------------
% 1.38/0.55  % (14523)------------------------------
% 1.38/0.55  % (14506)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.55  % (14508)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.55  % (14527)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (14528)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (14501)Refutation not found, incomplete strategy% (14501)------------------------------
% 1.38/0.55  % (14501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (14501)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (14501)Memory used [KB]: 10746
% 1.38/0.55  % (14501)Time elapsed: 0.141 s
% 1.38/0.55  % (14501)------------------------------
% 1.38/0.55  % (14501)------------------------------
% 1.38/0.55  % (14504)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.56  % (14519)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.56  % (14521)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.55/0.56  % (14522)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.55/0.56  % (14522)Refutation not found, incomplete strategy% (14522)------------------------------
% 1.55/0.56  % (14522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (14522)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (14522)Memory used [KB]: 1663
% 1.55/0.56  % (14522)Time elapsed: 0.145 s
% 1.55/0.56  % (14522)------------------------------
% 1.55/0.56  % (14522)------------------------------
% 1.55/0.56  % (14521)Refutation not found, incomplete strategy% (14521)------------------------------
% 1.55/0.56  % (14521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (14521)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (14521)Memory used [KB]: 10746
% 1.55/0.56  % (14521)Time elapsed: 0.142 s
% 1.55/0.56  % (14521)------------------------------
% 1.55/0.56  % (14521)------------------------------
% 1.55/0.56  % (14509)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.55/0.56  % (14529)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.55/0.56  % (14530)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.55/0.56  % (14513)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.55/0.56  % (14525)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.55/0.57  % (14510)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.55/0.58  % (14514)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.04/0.66  % (14527)Refutation found. Thanks to Tanya!
% 2.04/0.66  % SZS status Theorem for theBenchmark
% 2.04/0.66  % (14561)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.04/0.67  % SZS output start Proof for theBenchmark
% 2.04/0.67  fof(f1225,plain,(
% 2.04/0.67    $false),
% 2.04/0.67    inference(avatar_sat_refutation,[],[f102,f107,f112,f116,f163,f261,f465,f498,f1224])).
% 2.04/0.67  fof(f1224,plain,(
% 2.04/0.67    ~spl6_1 | spl6_2 | ~spl6_3 | ~spl6_4),
% 2.04/0.67    inference(avatar_contradiction_clause,[],[f1223])).
% 2.04/0.67  fof(f1223,plain,(
% 2.04/0.67    $false | (~spl6_1 | spl6_2 | ~spl6_3 | ~spl6_4)),
% 2.04/0.67    inference(subsumption_resolution,[],[f1222,f856])).
% 2.04/0.67  fof(f856,plain,(
% 2.04/0.67    r1_ordinal1(sK0,sK5(sK0,sK1)) | (~spl6_1 | spl6_2 | ~spl6_3 | ~spl6_4)),
% 2.04/0.67    inference(forward_demodulation,[],[f850,f617])).
% 2.04/0.67  fof(f617,plain,(
% 2.04/0.67    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f101,f526,f89])).
% 2.04/0.67  fof(f89,plain,(
% 2.04/0.67    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 2.04/0.67    inference(definition_unfolding,[],[f75,f55])).
% 2.04/0.67  fof(f55,plain,(
% 2.04/0.67    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 2.04/0.67    inference(cnf_transformation,[],[f3])).
% 2.04/0.67  fof(f3,axiom,(
% 2.04/0.67    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 2.04/0.67  fof(f75,plain,(
% 2.04/0.67    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 2.04/0.67    inference(cnf_transformation,[],[f48])).
% 2.04/0.67  fof(f48,plain,(
% 2.04/0.67    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.04/0.67    inference(flattening,[],[f47])).
% 2.04/0.67  fof(f47,plain,(
% 2.04/0.67    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.04/0.67    inference(nnf_transformation,[],[f8])).
% 2.04/0.67  fof(f8,axiom,(
% 2.04/0.67    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 2.04/0.67  fof(f526,plain,(
% 2.04/0.67    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),k2_xboole_0(sK0,k1_tarski(sK0))) | (~spl6_3 | ~spl6_4)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f49,f165,f505,f85])).
% 2.04/0.67  fof(f85,plain,(
% 2.04/0.67    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.04/0.67    inference(definition_unfolding,[],[f60,f55])).
% 2.04/0.67  fof(f60,plain,(
% 2.04/0.67    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f34])).
% 2.04/0.67  fof(f34,plain,(
% 2.04/0.67    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.04/0.67    inference(nnf_transformation,[],[f20])).
% 2.04/0.67  fof(f20,plain,(
% 2.04/0.67    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f12])).
% 2.04/0.67  fof(f12,axiom,(
% 2.04/0.67    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 2.04/0.67  fof(f505,plain,(
% 2.04/0.67    r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | (~spl6_3 | ~spl6_4)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f111,f49,f106,f84])).
% 2.04/0.67  fof(f84,plain,(
% 2.04/0.67    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.04/0.67    inference(definition_unfolding,[],[f57,f55])).
% 2.04/0.67  fof(f57,plain,(
% 2.04/0.67    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f33])).
% 2.04/0.67  fof(f33,plain,(
% 2.04/0.67    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.04/0.67    inference(nnf_transformation,[],[f19])).
% 2.04/0.67  fof(f19,plain,(
% 2.04/0.67    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f11])).
% 2.04/0.67  fof(f11,axiom,(
% 2.04/0.67    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 2.04/0.67  fof(f106,plain,(
% 2.04/0.67    r2_hidden(sK1,sK0) | ~spl6_3),
% 2.04/0.67    inference(avatar_component_clause,[],[f104])).
% 2.04/0.67  fof(f104,plain,(
% 2.04/0.67    spl6_3 <=> r2_hidden(sK1,sK0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.04/0.67  fof(f111,plain,(
% 2.04/0.67    v3_ordinal1(sK1) | ~spl6_4),
% 2.04/0.67    inference(avatar_component_clause,[],[f109])).
% 2.04/0.67  fof(f109,plain,(
% 2.04/0.67    spl6_4 <=> v3_ordinal1(sK1)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.04/0.67  fof(f165,plain,(
% 2.04/0.67    v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl6_4),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f111,f82])).
% 2.04/0.67  fof(f82,plain,(
% 2.04/0.67    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 2.04/0.67    inference(definition_unfolding,[],[f56,f55])).
% 2.04/0.67  fof(f56,plain,(
% 2.04/0.67    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f18])).
% 2.04/0.67  fof(f18,plain,(
% 2.04/0.67    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f10])).
% 2.04/0.67  fof(f10,axiom,(
% 2.04/0.67    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 2.04/0.67  fof(f49,plain,(
% 2.04/0.67    v3_ordinal1(sK0)),
% 2.04/0.67    inference(cnf_transformation,[],[f32])).
% 2.04/0.67  fof(f32,plain,(
% 2.04/0.67    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 2.04/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 2.04/0.67  fof(f30,plain,(
% 2.04/0.67    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 2.04/0.67    introduced(choice_axiom,[])).
% 2.04/0.67  fof(f31,plain,(
% 2.04/0.67    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 2.04/0.67    introduced(choice_axiom,[])).
% 2.04/0.67  fof(f29,plain,(
% 2.04/0.67    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 2.04/0.67    inference(rectify,[],[f28])).
% 2.04/0.67  fof(f28,plain,(
% 2.04/0.67    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 2.04/0.67    inference(flattening,[],[f27])).
% 2.04/0.67  fof(f27,plain,(
% 2.04/0.67    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 2.04/0.67    inference(nnf_transformation,[],[f17])).
% 2.04/0.67  fof(f17,plain,(
% 2.04/0.67    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 2.04/0.67    inference(flattening,[],[f16])).
% 2.04/0.67  fof(f16,plain,(
% 2.04/0.67    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f15])).
% 2.04/0.67  fof(f15,negated_conjecture,(
% 2.04/0.67    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 2.04/0.67    inference(negated_conjecture,[],[f14])).
% 2.04/0.67  fof(f14,conjecture,(
% 2.04/0.67    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 2.04/0.67  fof(f101,plain,(
% 2.04/0.67    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | spl6_2),
% 2.04/0.67    inference(avatar_component_clause,[],[f99])).
% 2.04/0.67  fof(f99,plain,(
% 2.04/0.67    spl6_2 <=> r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.04/0.67  fof(f850,plain,(
% 2.04/0.67    r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK5(sK0,sK1)) | (~spl6_1 | ~spl6_3 | ~spl6_4)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f111,f582,f782,f84])).
% 2.04/0.67  fof(f782,plain,(
% 2.04/0.67    v3_ordinal1(sK5(sK0,sK1)) | (~spl6_1 | ~spl6_3)),
% 2.04/0.67    inference(unit_resulting_resolution,[],[f49,f578,f63])).
% 2.04/0.67  fof(f63,plain,(
% 2.04/0.67    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f22])).
% 2.04/0.67  fof(f22,plain,(
% 2.04/0.67    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 2.04/0.67    inference(flattening,[],[f21])).
% 2.04/0.67  fof(f21,plain,(
% 2.04/0.67    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 2.04/0.67    inference(ennf_transformation,[],[f9])).
% 2.04/0.67  fof(f9,axiom,(
% 2.04/0.67    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 2.30/0.67  fof(f578,plain,(
% 2.30/0.67    r2_hidden(sK5(sK0,sK1),sK0) | (~spl6_1 | ~spl6_3)),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f106,f521])).
% 2.30/0.67  fof(f521,plain,(
% 2.30/0.67    ( ! [X6] : (~r2_hidden(X6,sK0) | r2_hidden(sK5(sK0,X6),sK0)) ) | ~spl6_1),
% 2.30/0.67    inference(superposition,[],[f91,f499])).
% 2.30/0.67  fof(f499,plain,(
% 2.30/0.67    sK0 = k3_tarski(sK0) | ~spl6_1),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f96,f61])).
% 2.30/0.67  fof(f61,plain,(
% 2.30/0.67    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f35])).
% 2.30/0.67  fof(f35,plain,(
% 2.30/0.67    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 2.30/0.67    inference(nnf_transformation,[],[f5])).
% 2.30/0.67  fof(f5,axiom,(
% 2.30/0.67    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 2.30/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).
% 2.30/0.67  fof(f96,plain,(
% 2.30/0.67    v4_ordinal1(sK0) | ~spl6_1),
% 2.30/0.67    inference(avatar_component_clause,[],[f95])).
% 2.30/0.67  fof(f95,plain,(
% 2.30/0.67    spl6_1 <=> v4_ordinal1(sK0)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.30/0.67  fof(f91,plain,(
% 2.30/0.67    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 2.30/0.67    inference(equality_resolution,[],[f70])).
% 2.30/0.67  fof(f70,plain,(
% 2.30/0.67    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 2.30/0.67    inference(cnf_transformation,[],[f46])).
% 2.30/0.67  fof(f46,plain,(
% 2.30/0.67    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3)) | ~r2_hidden(sK3(X0,X1),X1)) & ((r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),sK4(X0,X1))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK5(X0,X5),X0) & r2_hidden(X5,sK5(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.30/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f42,f45,f44,f43])).
% 2.30/0.67  fof(f43,plain,(
% 2.30/0.67    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3)) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK3(X0,X1),X4)) | r2_hidden(sK3(X0,X1),X1))))),
% 2.30/0.67    introduced(choice_axiom,[])).
% 2.30/0.67  fof(f44,plain,(
% 2.30/0.67    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK3(X0,X1),X4)) => (r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),sK4(X0,X1))))),
% 2.30/0.67    introduced(choice_axiom,[])).
% 2.30/0.67  fof(f45,plain,(
% 2.30/0.67    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK5(X0,X5),X0) & r2_hidden(X5,sK5(X0,X5))))),
% 2.30/0.67    introduced(choice_axiom,[])).
% 2.30/0.67  fof(f42,plain,(
% 2.30/0.67    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.30/0.67    inference(rectify,[],[f41])).
% 2.30/0.67  fof(f41,plain,(
% 2.30/0.67    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 2.30/0.67    inference(nnf_transformation,[],[f2])).
% 2.30/0.67  fof(f2,axiom,(
% 2.30/0.67    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.30/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 2.30/0.67  fof(f582,plain,(
% 2.30/0.67    r2_hidden(sK1,sK5(sK0,sK1)) | (~spl6_1 | ~spl6_3)),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f106,f522])).
% 2.30/0.67  fof(f522,plain,(
% 2.30/0.67    ( ! [X7] : (~r2_hidden(X7,sK0) | r2_hidden(X7,sK5(sK0,X7))) ) | ~spl6_1),
% 2.30/0.67    inference(superposition,[],[f92,f499])).
% 2.30/0.67  fof(f92,plain,(
% 2.30/0.67    ( ! [X0,X5] : (r2_hidden(X5,sK5(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 2.30/0.67    inference(equality_resolution,[],[f69])).
% 2.30/0.67  fof(f69,plain,(
% 2.30/0.67    ( ! [X0,X5,X1] : (r2_hidden(X5,sK5(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 2.30/0.67    inference(cnf_transformation,[],[f46])).
% 2.30/0.67  fof(f1222,plain,(
% 2.30/0.67    ~r1_ordinal1(sK0,sK5(sK0,sK1)) | (~spl6_1 | ~spl6_3)),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f49,f782,f784,f64])).
% 2.30/0.67  fof(f64,plain,(
% 2.30/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f36])).
% 2.30/0.67  fof(f36,plain,(
% 2.30/0.67    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.30/0.67    inference(nnf_transformation,[],[f24])).
% 2.30/0.67  fof(f24,plain,(
% 2.30/0.67    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.30/0.67    inference(flattening,[],[f23])).
% 2.30/0.67  fof(f23,plain,(
% 2.30/0.67    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.30/0.67    inference(ennf_transformation,[],[f6])).
% 2.30/0.67  fof(f6,axiom,(
% 2.30/0.67    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.30/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 2.30/0.67  fof(f784,plain,(
% 2.30/0.67    ~r1_tarski(sK0,sK5(sK0,sK1)) | (~spl6_1 | ~spl6_3)),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f578,f78])).
% 2.30/0.67  fof(f78,plain,(
% 2.30/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f26])).
% 2.30/0.67  fof(f26,plain,(
% 2.30/0.67    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.30/0.67    inference(ennf_transformation,[],[f13])).
% 2.30/0.67  fof(f13,axiom,(
% 2.30/0.67    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.30/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.30/0.67  fof(f498,plain,(
% 2.30/0.67    spl6_1 | ~spl6_5 | ~spl6_6),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f497])).
% 2.30/0.67  fof(f497,plain,(
% 2.30/0.67    $false | (spl6_1 | ~spl6_5 | ~spl6_6)),
% 2.30/0.67    inference(subsumption_resolution,[],[f496,f471])).
% 2.30/0.67  fof(f471,plain,(
% 2.30/0.67    ~r2_hidden(k2_xboole_0(sK3(sK0,sK0),k1_tarski(sK3(sK0,sK0))),sK0) | (spl6_1 | ~spl6_6)),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f180,f81,f158,f74])).
% 2.30/0.67  fof(f74,plain,(
% 2.30/0.67    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f46])).
% 2.30/0.67  fof(f158,plain,(
% 2.30/0.67    r2_hidden(sK3(sK0,sK0),sK0) | ~spl6_6),
% 2.30/0.67    inference(avatar_component_clause,[],[f156])).
% 2.30/0.67  fof(f156,plain,(
% 2.30/0.67    spl6_6 <=> r2_hidden(sK3(sK0,sK0),sK0)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.30/0.67  fof(f81,plain,(
% 2.30/0.67    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 2.30/0.67    inference(definition_unfolding,[],[f54,f55])).
% 2.30/0.67  fof(f54,plain,(
% 2.30/0.67    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 2.30/0.67    inference(cnf_transformation,[],[f7])).
% 2.30/0.67  fof(f7,axiom,(
% 2.30/0.67    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 2.30/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 2.30/0.67  fof(f180,plain,(
% 2.30/0.67    sK0 != k3_tarski(sK0) | spl6_1),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f97,f62])).
% 2.30/0.67  fof(f62,plain,(
% 2.30/0.67    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 2.30/0.67    inference(cnf_transformation,[],[f35])).
% 2.30/0.67  fof(f97,plain,(
% 2.30/0.67    ~v4_ordinal1(sK0) | spl6_1),
% 2.30/0.67    inference(avatar_component_clause,[],[f95])).
% 2.30/0.67  fof(f496,plain,(
% 2.30/0.67    r2_hidden(k2_xboole_0(sK3(sK0,sK0),k1_tarski(sK3(sK0,sK0))),sK0) | (~spl6_5 | ~spl6_6)),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f158,f473,f115])).
% 2.30/0.67  fof(f115,plain,(
% 2.30/0.67    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0)) ) | ~spl6_5),
% 2.30/0.67    inference(avatar_component_clause,[],[f114])).
% 2.30/0.67  fof(f114,plain,(
% 2.30/0.67    spl6_5 <=> ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.30/0.67  fof(f473,plain,(
% 2.30/0.67    v3_ordinal1(sK3(sK0,sK0)) | ~spl6_6),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f49,f158,f63])).
% 2.30/0.67  fof(f465,plain,(
% 2.30/0.67    spl6_6 | ~spl6_7 | ~spl6_8),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f464])).
% 2.30/0.67  fof(f464,plain,(
% 2.30/0.67    $false | (spl6_6 | ~spl6_7 | ~spl6_8)),
% 2.30/0.67    inference(subsumption_resolution,[],[f455,f426])).
% 2.30/0.67  fof(f426,plain,(
% 2.30/0.67    ~r1_ordinal1(sK4(sK0,sK0),sK0) | (spl6_6 | ~spl6_7 | ~spl6_8)),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f49,f283,f298,f64])).
% 2.30/0.67  fof(f298,plain,(
% 2.30/0.67    ~r1_tarski(sK4(sK0,sK0),sK0) | (spl6_6 | ~spl6_8)),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f157,f260,f66])).
% 2.30/0.67  fof(f66,plain,(
% 2.30/0.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f40])).
% 2.30/0.67  fof(f40,plain,(
% 2.30/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.30/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 2.30/0.67  fof(f39,plain,(
% 2.30/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.30/0.67    introduced(choice_axiom,[])).
% 2.30/0.67  fof(f38,plain,(
% 2.30/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.30/0.67    inference(rectify,[],[f37])).
% 2.30/0.67  fof(f37,plain,(
% 2.30/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.30/0.67    inference(nnf_transformation,[],[f25])).
% 2.30/0.67  fof(f25,plain,(
% 2.30/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.30/0.67    inference(ennf_transformation,[],[f1])).
% 2.30/0.67  fof(f1,axiom,(
% 2.30/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.30/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.30/0.67  fof(f260,plain,(
% 2.30/0.67    r2_hidden(sK3(sK0,sK0),sK4(sK0,sK0)) | ~spl6_8),
% 2.30/0.67    inference(avatar_component_clause,[],[f258])).
% 2.30/0.67  fof(f258,plain,(
% 2.30/0.67    spl6_8 <=> r2_hidden(sK3(sK0,sK0),sK4(sK0,sK0))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.30/0.67  fof(f157,plain,(
% 2.30/0.67    ~r2_hidden(sK3(sK0,sK0),sK0) | spl6_6),
% 2.30/0.67    inference(avatar_component_clause,[],[f156])).
% 2.30/0.67  fof(f283,plain,(
% 2.30/0.67    v3_ordinal1(sK4(sK0,sK0)) | ~spl6_7),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f49,f162,f63])).
% 2.30/0.67  fof(f162,plain,(
% 2.30/0.67    r2_hidden(sK4(sK0,sK0),sK0) | ~spl6_7),
% 2.30/0.67    inference(avatar_component_clause,[],[f160])).
% 2.30/0.67  fof(f160,plain,(
% 2.30/0.67    spl6_7 <=> r2_hidden(sK4(sK0,sK0),sK0)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.30/0.67  fof(f455,plain,(
% 2.30/0.67    r1_ordinal1(sK4(sK0,sK0),sK0) | ~spl6_7),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f49,f283,f286,f86])).
% 2.30/0.67  fof(f86,plain,(
% 2.30/0.67    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.30/0.67    inference(definition_unfolding,[],[f59,f55])).
% 2.30/0.67  fof(f59,plain,(
% 2.30/0.67    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f286,plain,(
% 2.30/0.67    r2_hidden(sK4(sK0,sK0),k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl6_7),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f162,f88])).
% 2.30/0.67  fof(f88,plain,(
% 2.30/0.67    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 2.30/0.67    inference(definition_unfolding,[],[f76,f55])).
% 2.30/0.67  fof(f76,plain,(
% 2.30/0.67    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f48])).
% 2.30/0.67  fof(f261,plain,(
% 2.30/0.67    spl6_6 | spl6_8 | spl6_1),
% 2.30/0.67    inference(avatar_split_clause,[],[f256,f95,f258,f156])).
% 2.30/0.67  fof(f256,plain,(
% 2.30/0.67    r2_hidden(sK3(sK0,sK0),sK4(sK0,sK0)) | r2_hidden(sK3(sK0,sK0),sK0) | spl6_1),
% 2.30/0.67    inference(equality_resolution,[],[f192])).
% 2.30/0.67  fof(f192,plain,(
% 2.30/0.67    ( ! [X0] : (sK0 != X0 | r2_hidden(sK3(sK0,X0),sK4(sK0,X0)) | r2_hidden(sK3(sK0,X0),X0)) ) | spl6_1),
% 2.30/0.67    inference(superposition,[],[f180,f72])).
% 2.30/0.67  fof(f72,plain,(
% 2.30/0.67    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(sK3(X0,X1),X1)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f46])).
% 2.30/0.67  fof(f163,plain,(
% 2.30/0.67    spl6_6 | spl6_7 | spl6_1),
% 2.30/0.67    inference(avatar_split_clause,[],[f154,f95,f160,f156])).
% 2.30/0.67  fof(f154,plain,(
% 2.30/0.67    r2_hidden(sK4(sK0,sK0),sK0) | r2_hidden(sK3(sK0,sK0),sK0) | spl6_1),
% 2.30/0.67    inference(equality_resolution,[],[f127])).
% 2.30/0.67  fof(f127,plain,(
% 2.30/0.67    ( ! [X1] : (sK0 != X1 | r2_hidden(sK4(sK0,X1),sK0) | r2_hidden(sK3(sK0,X1),X1)) ) | spl6_1),
% 2.30/0.67    inference(superposition,[],[f122,f73])).
% 2.30/0.67  fof(f73,plain,(
% 2.30/0.67    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK4(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f46])).
% 2.30/0.67  fof(f122,plain,(
% 2.30/0.67    sK0 != k3_tarski(sK0) | spl6_1),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f97,f62])).
% 2.30/0.67  fof(f116,plain,(
% 2.30/0.67    spl6_1 | spl6_5),
% 2.30/0.67    inference(avatar_split_clause,[],[f80,f114,f95])).
% 2.30/0.67  fof(f80,plain,(
% 2.30/0.67    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 2.30/0.67    inference(definition_unfolding,[],[f50,f55])).
% 2.30/0.67  fof(f50,plain,(
% 2.30/0.67    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f32])).
% 2.30/0.67  fof(f112,plain,(
% 2.30/0.67    ~spl6_1 | spl6_4),
% 2.30/0.67    inference(avatar_split_clause,[],[f51,f109,f95])).
% 2.30/0.67  fof(f51,plain,(
% 2.30/0.67    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 2.30/0.67    inference(cnf_transformation,[],[f32])).
% 2.30/0.67  fof(f107,plain,(
% 2.30/0.67    ~spl6_1 | spl6_3),
% 2.30/0.67    inference(avatar_split_clause,[],[f52,f104,f95])).
% 2.30/0.67  fof(f52,plain,(
% 2.30/0.67    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 2.30/0.67    inference(cnf_transformation,[],[f32])).
% 2.30/0.67  fof(f102,plain,(
% 2.30/0.67    ~spl6_1 | ~spl6_2),
% 2.30/0.67    inference(avatar_split_clause,[],[f79,f99,f95])).
% 2.30/0.67  fof(f79,plain,(
% 2.30/0.67    ~r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v4_ordinal1(sK0)),
% 2.30/0.67    inference(definition_unfolding,[],[f53,f55])).
% 2.30/0.67  fof(f53,plain,(
% 2.30/0.67    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 2.30/0.67    inference(cnf_transformation,[],[f32])).
% 2.30/0.67  % SZS output end Proof for theBenchmark
% 2.30/0.67  % (14527)------------------------------
% 2.30/0.67  % (14527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.67  % (14527)Termination reason: Refutation
% 2.30/0.67  
% 2.30/0.67  % (14527)Memory used [KB]: 11769
% 2.30/0.67  % (14527)Time elapsed: 0.258 s
% 2.30/0.67  % (14527)------------------------------
% 2.30/0.67  % (14527)------------------------------
% 2.30/0.68  % (14493)Success in time 0.316 s
%------------------------------------------------------------------------------
